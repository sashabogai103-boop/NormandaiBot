#!/usr/bin/env python3
"""
Бот сигналов v2 для ручной торговли (FxPro MT5) -> Telegram.

Работает в GitHub Actions: одна задача живёт ~55 минут и крутит цикл
(следующая стартует по расписанию и подхватывает эстафету), поэтому:
  * анализ запускается сразу после закрытия свечи M5 (а не «когда GitHub вспомнит»);
  * бот читает твои сообщения в Telegram и отвечает за секунды (команды /gold, /news ...);
  * новости из календаря входят в план: предупреждение за час, заморозка входов
    за 10 минут до выхода данных, тактика T5 (вход на откате после реакции рынка).

Тактики (без угадывания, каждая с чёткими условиями):
  T1  свип ликвидности: прокол уровня (хай/лой вчера, Азии, свинга, круглый)
      + закрытие M5 обратно + слом мини-структуры.
  T2  пробой и ретест по тренду H1.
  T5  после новости: настоящая реакция (>=2 ATR) -> вход на откате 38-62% импульса.
  ГОТОВЬСЯ: цена подошла к уровню / идёт откат после новости.

Данные: Twelve Data (бесплатный ключ, 800 запросов/сутки) и календарь новостей
(бесплатный JSON). Цены не равны FxPro: всегда сверяй цену и спред в MT5.
Бот сделок не открывает. Объём входа решаешь только ты.
"""
import html
import json
import math
import os
import re
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import deque
from datetime import datetime, timedelta, timezone

VERSION = "2.0"

# ---------------------------------------------------------------- настройки
TWELVE_KEY = os.environ.get("TWELVE_KEY", "").strip()
TG_TOKEN = os.environ.get("TG_TOKEN", "").strip()
TG_CHAT = os.environ.get("TG_CHAT", "").strip()
STATE_FILE = os.environ.get("STATE_FILE", "state.json")
OFFLINE_DIR = os.environ.get("OFFLINE_DIR", "")   # для тестов: csv вместо API
DRY = os.environ.get("DRY", "") == "1"            # печатать в консоль, не слать в Telegram
RUN_SECONDS = int(os.environ.get("RUN_SECONDS", "3300"))  # сколько живёт один запуск

# Защита от ошибок вставки секретов (лишние слова/пробелы)
_m = re.search(r"\d{6,}:[A-Za-z0-9_-]{30,}", TG_TOKEN)
if _m:
    TG_TOKEN = _m.group(0)
_m = re.search(r"-?\d+", TG_CHAT)
TG_CHAT = _m.group(0) if _m else ""


def _kyiv():
    try:
        from zoneinfo import ZoneInfo
        for name in ("Europe/Kyiv", "Europe/Kiev"):
            try:
                return ZoneInfo(name)
            except Exception:
                pass
    except Exception:
        pass
    return timezone(timedelta(hours=2))


KYIV = _kyiv()

# value_per_lot = сколько $ даёт движение цены на 1.00 при объёме 1.00 лот.
# ПРОВЕРЬ в MT5: Market Watch -> символ -> Спецификация (Contract size).
INSTRUMENTS = {
    "XAU/USD": {"mt5": "GOLD", "name": "Золото", "icon": "🥇",
                "value_per_lot": 100, "min_lot": 0.01, "spread": 0.15,
                "every_min": 5, "sessions": [(9, 13), (15, 19)],
                "weekdays_only": True, "rollover": True, "round": 50.0},
    "BTC/USD": {"mt5": "BITCOIN", "name": "Биткоин", "icon": "🟠",
                "value_per_lot": 1, "min_lot": 0.01, "spread": 15.4,
                "every_min": 10, "sessions": None, "round": 1000.0},
    "ETH/USD": {"mt5": "ETHEREUM", "name": "Эфир", "icon": "🔷",
                "value_per_lot": 1, "min_lot": 0.1, "spread": 3.0,
                "every_min": 10, "sessions": None, "round": 50.0},
    "SPCX":    {"mt5": "SPCX.O", "name": "SpaceX", "icon": "🚀",
                "value_per_lot": 1, "min_lot": 1, "spread": 0.47,
                "every_min": 10, "sessions": [(16, 23)],
                "weekdays_only": True, "rollover": True, "round": 5.0},
    # SOLANA отключена: спред ~0.8% цены съедает стоп.
}
ALIASES = {  # подстрока -> инструмент (для свободного текста и команд)
    "gold": "XAU/USD", "xau": "XAU/USD", "золот": "XAU/USD",
    "btc": "BTC/USD", "bitcoin": "BTC/USD", "бит": "BTC/USD",
    "eth": "ETH/USD", "ethereum": "ETH/USD", "эфир": "ETH/USD",
    "spcx": "SPCX", "spacex": "SPCX", "спейс": "SPCX",
}

MAX_SPREAD_SHARE = 0.15       # спред не больше 15% стопа
MIN_R = 1.5
MIN_SCORE = 7.0               # = 3.5 звезды из 5
MAX_TRADES_DAY = 4            # не больше 4 сигналов на инструмент в день
MAX_PREPS_DAY = 6             # и не больше 6 «ГОТОВЬСЯ»
TRADE_PAUSE_MIN = 30          # пауза после сигнала по инструменту
ROLLOVER = ((23, 30), (1, 30))        # Киев, только золото и SpaceX
FALLBACK_NEWS_BLOCK = ((15, 25), (15, 45))  # если календарь недоступен
NEWS_BEFORE, NEWS_AFTER = 10, 10      # минуты заморозки входов вокруг High-новости
DAILY_LIMIT = 780             # бесплатный лимит Twelve Data 800/сутки
SCAN_DELAY = 12               # сек. после закрытия свечи до анализа
CALENDAR_URLS = ["https://nfs.faireconomy.media/ff_calendar_thisweek.json",
                 "https://nfs.faireconomy.media/ff_calendar_nextweek.json"]

STATE = {}
CHAT = None
CACHE = {}
LAST_SLOT = {}
EVENTS = []
_calls = deque()
UA = {"User-Agent": "Mozilla/5.0 (signal-bot v2)"}


# ---------------------------------------------------------------- утилиты
def fmt(x, d=2):
    return f"{x:,.{d}f}".replace(",", " ")


def kyiv(dt):
    return dt.astimezone(KYIV)


def hhmm(dt):
    return kyiv(dt).strftime("%H:%M")


def esc(s):
    return html.escape(str(s), quote=False)


def in_window(now_k, start, end):
    m = now_k.hour * 60 + now_k.minute
    s = start[0] * 60 + start[1]
    e = end[0] * 60 + end[1]
    return s <= m < e if s < e else (m >= s or m < e)


def http_json(url, params=None, data=None, timeout=20):
    if params:
        url = f"{url}?{urllib.parse.urlencode(params)}"
    req = urllib.request.Request(url, data=data, headers=UA)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


# ---------------------------------------------------------------- данные
def api_counter():
    day = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    a = STATE.setdefault("api", {})
    if a.get("day") != day:
        a["day"], a["n"] = day, 0
    return a


def td_series(symbol, interval, n):
    a = api_counter()
    if a["n"] >= DAILY_LIMIT:
        raise RuntimeError("дневной лимит Twelve Data исчерпан")
    now = time.time()
    while _calls and now - _calls[0] > 60:
        _calls.popleft()
    if len(_calls) >= 7:  # бесплатно: 8 запросов в минуту
        time.sleep(max(0.0, 60 - (now - _calls[0])) + 0.5)
    _calls.append(time.time())
    a["n"] += 1
    js = http_json("https://api.twelvedata.com/time_series", {
        "symbol": symbol, "interval": interval, "outputsize": n,
        "timezone": "UTC", "apikey": TWELVE_KEY})
    if js.get("status") == "error":
        raise RuntimeError(js.get("message", "ошибка API"))
    return js["values"]


def parse_bars(values):
    bars = []
    for v in values:
        bars.append({
            "t": datetime.strptime(v["datetime"][:19], "%Y-%m-%d %H:%M:%S")
                 .replace(tzinfo=timezone.utc),
            "o": float(v["open"]), "h": float(v["high"]),
            "l": float(v["low"]), "c": float(v["close"])})
    bars.sort(key=lambda b: b["t"])
    return bars


def load_csv(symbol):
    fn = os.path.join(OFFLINE_DIR, symbol.replace("/", "") + ".csv")
    rows = [ln.strip().split(";") for ln in open(fn) if ln[:1].isdigit()]
    return parse_bars([{"datetime": r[0], "open": r[1], "high": r[2],
                        "low": r[3], "close": r[4]} for r in rows])


def get_bars(sym, interval, n, max_age):
    """Свечи (старые -> новые). Кэш в памяти на max_age секунд."""
    key = (sym, interval)
    c = CACHE.get(key)
    if c and time.time() - c[0] <= max_age:
        return c[1]
    if OFFLINE_DIR:
        m5 = load_csv(sym)
        bars = m5 if interval == "5min" else resample(m5, 60)
    else:
        bars = parse_bars(td_series(sym, interval, n))
    CACHE[key] = (time.time(), bars)
    return bars


def get_h1(sym):
    try:
        return get_bars(sym, "1h", 150, 1800)
    except Exception as e:
        print(sym, "H1 недоступен:", e)
        c = CACHE.get((sym, "1h"))
        return c[1] if c else None


def closed_bars(bars, now_u, minutes):
    d = timedelta(minutes=minutes)
    return [b for b in bars if b["t"] + d <= now_u]


def resample(bars, minutes):
    out, cur = [], None
    for b in bars:
        t = b["t"]
        if minutes < 60:
            key = t.replace(minute=(t.minute // minutes) * minutes,
                            second=0, microsecond=0)
        else:
            step = minutes // 60
            key = t.replace(hour=(t.hour // step) * step, minute=0,
                            second=0, microsecond=0)
        if cur is None or cur["t"] != key:
            if cur:
                out.append(cur)
            cur = {"t": key, "o": b["o"], "h": b["h"], "l": b["l"], "c": b["c"]}
        else:
            cur["h"] = max(cur["h"], b["h"])
            cur["l"] = min(cur["l"], b["l"])
            cur["c"] = b["c"]
    if cur:
        out.append(cur)
    return out


def atr(bars, n=14):
    trs = []
    for i in range(1, len(bars)):
        p, b = bars[i - 1]["c"], bars[i]
        trs.append(max(b["h"] - b["l"], abs(b["h"] - p), abs(b["l"] - p)))
    trs = trs[-n:]
    return sum(trs) / len(trs) if trs else 0.0


def ema(vals, n):
    k = 2 / (n + 1)
    e = vals[0]
    for v in vals[1:]:
        e = v * k + e * (1 - k)
    return e


def trend_of(closes, n=20, lag=3):
    """+1 вверх, -1 вниз, 0 нет тренда: цена по сторону EMA и EMA наклонена."""
    if len(closes) < n + lag + 5:
        return 0
    e_now = ema(closes[-n * 2:], n)
    e_prev = ema(closes[-n * 2 - lag:-lag], n)
    if closes[-1] > e_now and e_now > e_prev:
        return 1
    if closes[-1] < e_now and e_now < e_prev:
        return -1
    return 0


def build_ctx(closed, h1_raw, now_u):
    """Контекст старших таймфреймов: тренд H1/H4, ATR H1, режим рынка, ход дня."""
    if h1_raw and len(h1_raw) >= 30:
        h1c = closed_bars(h1_raw, now_u, 60)
    else:
        h1c = closed_bars(resample(closed, 60), now_u, 60)
    h4c = closed_bars(resample(h1c, 240), now_u, 240)
    ctx = {"h1": trend_of([b["c"] for b in h1c]),
           "h4": trend_of([b["c"] for b in h4c]),
           "a60": atr(h1c, 14) if len(h1c) > 15 else 0.0}
    # режим рынка: текущий ATR M5 против среднего за сутки
    trs = []
    for i in range(1, len(closed)):
        p, b = closed[i - 1]["c"], closed[i]
        trs.append(max(b["h"] - b["l"], abs(b["h"] - p), abs(b["l"] - p)))
    trs = trs[-288:]
    mean_tr = sum(trs) / len(trs) if trs else 0
    a5 = atr(closed, 14)
    ctx["regime"] = (a5 / mean_tr) if mean_tr else None
    # ход дня против среднего дневного диапазона (по H1)
    today = closed[-1]["t"].date()
    days = {}
    for b in h1c:
        d = b["t"].date()
        if d < today:
            lo_hi = days.setdefault(d, [b["l"], b["h"]])
            lo_hi[0], lo_hi[1] = min(lo_hi[0], b["l"]), max(lo_hi[1], b["h"])
    rngs = [v[1] - v[0] for k, v in sorted(days.items())][-4:]
    avg_dr = sum(rngs) / len(rngs) if len(rngs) >= 2 else 0
    td = [b for b in closed if b["t"].date() == today]
    t_rng = (max(b["h"] for b in td) - min(b["l"] for b in td)) if td else 0
    ctx["day_ratio"] = (t_rng / avg_dr) if avg_dr else None
    return ctx


# ---------------------------------------------------------------- уровни
def key_levels(closed, spec, ref):
    """Уровни ликвидности: вчера, Азия, свинги 5ч, круглые. ref - цена для
    определения стороны круглого уровня. Близкие уровни одной стороны склеиваются."""
    a5 = atr(closed, 14)
    last = closed[-1]["t"]
    today = last.date()
    prior = sorted({b["t"].date() for b in closed if b["t"].date() < today})
    y_bars = []
    for d in reversed(prior):
        cand = [b for b in closed if b["t"].date() == d]
        if len(cand) >= 100:  # полноценный торговый день, не огрызок воскресенья
            y_bars = cand
            break
    asia = [b for b in closed if b["t"].date() == today and b["t"].hour < 7]
    lv = []
    if y_bars:
        lv += [("хай вчера", max(b["h"] for b in y_bars), "high"),
               ("лой вчера", min(b["l"] for b in y_bars), "low")]
    if asia and last.hour >= 7:
        lv += [("хай Азии", max(b["h"] for b in asia), "high"),
               ("лой Азии", min(b["l"] for b in asia), "low")]
    window = closed[-60:-6]
    if window:
        lv += [("свинг-хай 5ч", max(b["h"] for b in window), "high"),
               ("свинг-лой 5ч", min(b["l"] for b in window), "low")]
    step = spec.get("round")
    if step:
        base = math.floor(ref / step) * step
        for L in (base - step, base, base + step, base + 2 * step):
            lv.append(("круглый уровень", L, "low" if ref >= L else "high"))
    merged = []
    for name, L, side in lv:
        for m in merged:
            if m[2] == side and abs(m[1] - L) < 0.1 * a5:
                m[0] = (name + " + " + m[0]) if m[0].startswith("свинг") \
                    and not name.startswith("свинг") else m[0] + " + " + name
                break
        else:
            merged.append([name, L, side])
    return [tuple(m) for m in merged]


# ---------------------------------------------------------------- сетапы
def make(tac, d, lname, lvl, entry, sl, tp, ctx, bonus, quiet=False):
    sgn = 1 if d == "LONG" else -1
    risk, reward = abs(entry - sl), abs(tp - entry)
    rr = reward / risk if risk else 0
    score, reasons = 6.5, []
    for pts, txt in bonus:
        score += pts
        reasons.append(txt)
    h1, h4 = ctx["h1"], ctx["h4"]
    if h1 == sgn:
        score += 0.75
        txt = "по тренду H1"
        if h4 == sgn:
            score += 0.25
            txt += " и H4"
        reasons.append(txt)
    elif h1 == -sgn:
        score -= 0.5
        txt = "против тренда H1"
        if h4 == -sgn:
            score -= 0.25
            txt += " и H4"
        reasons.append(txt + " (минус к оценке)")
    if quiet:
        score -= 0.5
        reasons.append("вялый рынок: хода может не хватить")
    if rr >= 2:
        score += 0.5
    if rr < MIN_R:
        score -= 1.5
        reasons.append(f"R:R всего {rr:.1f}")
    return {"kind": "TRADE", "tactic": tac, "dir": d, "level_name": lname,
            "level": lvl, "entry": entry, "sl": sl, "tp": tp, "rr": rr,
            "score": round(max(0, min(score, 10)), 2), "reasons": reasons}


def pick_target(levels, entry, risk, d):
    """Цель: ближайший уровень дальше 1.5R; иначе 2R. Плюс ближайшее препятствие."""
    if d == "LONG":
        ahead = sorted([l for l in levels if l[1] > entry], key=lambda l: l[1])
    else:
        ahead = sorted([l for l in levels if l[1] < entry],
                       key=lambda l: -l[1])
    far = [l for l in ahead if abs(l[1] - entry) >= 1.5 * risk]
    if far:
        tp = far[0][1]
    else:
        tp = entry + 2 * risk if d == "LONG" else entry - 2 * risk
    obst = [l for l in ahead if 0.4 * risk <= abs(l[1] - entry) < abs(tp - entry) - 1e-9]
    return tp, (obst[0] if obst else None)


def find_setups(sym, spec, closed, ctx):
    out = []
    if len(closed) < 60:
        return out
    a5 = atr(closed, 14)
    if not a5:
        return out
    b, prev = closed[-1], closed[-2]
    a60 = ctx["a60"] or a5 * 3.4
    h1 = ctx["h1"]
    levels = key_levels(closed, spec, prev["c"])
    recent, older, last3 = closed[-7:-1], closed[-19:-7], closed[-4:-1]
    rng = b["h"] - b["l"]
    spike = rng > 4.5 * a5          # новостной спайк: не торгуем
    quiet = ctx["regime"] is not None and ctx["regime"] < 0.6
    for name, lvl, side in levels:
        if not spike and rng:
            upper = (b["c"] - b["l"]) / rng >= 0.6
            lower = (b["h"] - b["c"]) / rng >= 0.6
            low_wick = min(b["o"], b["c"]) - b["l"]
            up_wick = b["h"] - max(b["o"], b["c"])
            swing_only = name.startswith("свинг")
            strong = ("вчера" in name) or ("Азии" in name)
            rnd = "круглый" in name
            bonus = [(1.0, f"прокол «{name}» и возврат, структура M5 сломана "
                           f"в сторону сделки")]
            if strong:
                bonus.append((0.5, "снята ликвидность за сильным уровнем"))
            if rnd:
                bonus.append((0.25, "снят круглый уровень"))
            # ---- T1 свип вверх по лою: LONG
            if side == "low" and b["l"] < lvl - 0.05 * a5 and b["c"] > lvl \
                    and upper and low_wick >= 0.25 * a5 \
                    and b["c"] > max(x["h"] for x in last3) \
                    and (not swing_only or h1 == 1):
                entry, sl = b["c"], b["l"] - 0.15 * a5
                tp, ob = pick_target(levels, entry, entry - sl, "LONG")
                s = make("T1 свип", "LONG", name, lvl, entry, sl, tp, ctx,
                         bonus, quiet)
                s["obstacle"] = ob
                out.append(s)
            # ---- T1 свип хая: SHORT
            if side == "high" and b["h"] > lvl + 0.05 * a5 and b["c"] < lvl \
                    and lower and up_wick >= 0.25 * a5 \
                    and b["c"] < min(x["l"] for x in last3) \
                    and (not swing_only or h1 == -1):
                entry, sl = b["c"], b["h"] + 0.15 * a5
                tp, ob = pick_target(levels, entry, sl - entry, "SHORT")
                s = make("T1 свип", "SHORT", name, lvl, entry, sl, tp, ctx,
                         bonus, quiet)
                s["obstacle"] = ob
                out.append(s)
            # ---- T2 пробой + ретест по тренду H1 (не для круглых)
            if not rnd:
                broke_up = any(x["c"] > lvl for x in recent) and \
                    min(x["l"] for x in older) < lvl
                if side == "high" and h1 == 1 and broke_up and \
                        b["l"] <= lvl + 0.2 * a5 and b["c"] > lvl and b["c"] > b["o"]:
                    entry, sl = b["c"], min(b["l"], prev["l"]) - 0.2 * a5
                    out.append(make(
                        "T2 ретест", "LONG", name, lvl, entry, sl,
                        entry + 2 * (entry - sl), ctx,
                        [(1.0, f"пробой «{name}» и ретест сверху")], quiet))
                broke_dn = any(x["c"] < lvl for x in recent) and \
                    max(x["h"] for x in older) > lvl
                if side == "low" and h1 == -1 and broke_dn and \
                        b["h"] >= lvl - 0.2 * a5 and b["c"] < lvl and b["c"] < b["o"]:
                    entry, sl = b["c"], max(b["h"], prev["h"]) + 0.2 * a5
                    out.append(make(
                        "T2 ретест", "SHORT", name, lvl, entry, sl,
                        entry - 2 * (sl - entry), ctx,
                        [(1.0, f"пробой «{name}» и ретест снизу")], quiet))
        # ---- ГОТОВЬСЯ: цена близко к уровню, свипа ещё нет
        dist = abs(b["c"] - lvl)
        zone = closed[-5:]
        untouched = (side == "low" and min(x["l"] for x in zone) > lvl) \
            or (side == "high" and max(x["h"] for x in zone) < lvl)
        thr = 0.2 if name == "круглый уровень" else 0.35  # чистые круглые: строже
        if untouched and dist < thr * a60:
            out.append({"kind": "PREP", "level_name": name, "level": lvl,
                        "side": side, "price": b["c"], "atr60": a60})
    best, preps = {}, {}
    for s in out:
        if s["kind"] == "TRADE":
            if s["dir"] not in best or s["score"] > best[s["dir"]]["score"]:
                best[s["dir"]] = s
        else:
            k = s["side"]
            if k not in preps or abs(s["price"] - s["level"]) < \
                    abs(preps[k]["price"] - preps[k]["level"]):
                preps[k] = s
    if len(best) == 2:  # сигналы в обе стороны = неясно, ничего не даём
        best = {}
    return list(best.values()) + ([] if best else list(preps.values()))


def news_setups(sym, spec, closed, ctx):
    """T5: после настоящей реакции на High-новость ищем вход на откате."""
    out = []
    if len(closed) < 40 or not EVENTS:
        return out
    a5 = atr(closed, 14)
    b, prev = closed[-1], closed[-2]
    b_end = b["t"] + timedelta(minutes=5)
    for t0, evs in high_groups().items():
        title = evs[0]["title"] + (f" (+{len(evs) - 1})" if len(evs) > 1 else "")
        since = (b_end - t0).total_seconds() / 60
        if not (10 <= since <= 80):
            continue
        imp = [x for x in closed if t0 <= x["t"] < t0 + timedelta(minutes=10)]
        before = [x for x in closed if x["t"] < t0][-15:]
        if len(imp) < 2 or len(before) < 10:
            continue
        a0 = atr(before, 14)
        hi, lo = max(x["h"] for x in imp), min(x["l"] for x in imp)
        rng = hi - lo
        if a0 <= 0 or rng < 2.0 * a0:
            continue                      # реакции нет, торговать нечего
        move = imp[-1]["c"] - imp[0]["o"]
        if abs(move) < 0.4 * rng:
            continue                      # импульс без направления
        d = 1 if move > 0 else -1
        after = [x for x in closed if x["t"] >= t0 + timedelta(minutes=10)]
        if not after:
            continue
        if d == 1:
            zl, zh = hi - 0.618 * rng, hi - 0.382 * rng
            failed = any(x["c"] < lo + 0.25 * rng for x in after)
            chased = max(x["h"] for x in after) > hi + 0.1 * rng
        else:
            zl, zh = lo + 0.382 * rng, lo + 0.618 * rng
            failed = any(x["c"] > hi - 0.25 * rng for x in after)
            chased = min(x["l"] for x in after) < lo - 0.1 * rng
        if failed or chased:
            continue                      # импульс сломан или ушёл без отката
        ek = t0.strftime("%Y%m%d%H%M") + "|" + evs[0]["title"]
        confirm = (d == 1 and b["l"] <= zh and b["c"] > b["o"] and b["c"] > zl) \
            or (d == -1 and b["h"] >= zl and b["c"] < b["o"] and b["c"] < zh)
        if confirm:
            entry = b["c"]
            if d == 1:
                sl = min(b["l"], prev["l"]) - 0.2 * a5
                tp = hi + 0.27 * rng
            else:
                sl = max(b["h"], prev["h"]) + 0.2 * a5
                tp = lo - 0.27 * rng
            risk = abs(entry - sl)
            if risk <= 0 or (d == 1 and tp <= entry) or (d == -1 and tp >= entry):
                continue
            bonus = [(0.0, f"реакция на «{title}»: импульс "
                           f"{rng / a0:.1f}×ATR, вход на откате 38–62%")]
            if rng >= 3 * a0:
                bonus.append((0.25, "сильная реакция рынка"))
            s = make("T5 после новости", "LONG" if d == 1 else "SHORT",
                     "откат импульса", (zl + zh) / 2, entry, sl, tp, ctx, bonus)
            s["ev"] = ek
            out.append(s)
        elif since <= 60:
            out.append({"kind": "PREP", "news": True, "key": ek,
                        "title": title, "t0": t0, "dir": d,
                        "zone": (zl, zh), "ext": hi if d == 1 else lo,
                        "rng": rng, "k": rng / a0, "price": b["c"],
                        "level": (zl + zh) / 2, "level_name": "откат импульса",
                        "side": "low" if d == 1 else "high"})
    return out


# ---------------------------------------------------------------- риск
def size(spec, s):
    """Справка: $ риска/профита на минимальный лот. Объём решает трейдер."""
    dist = abs(s["entry"] - s["sl"])
    if dist <= 0 or spec.get("spread", 0) > MAX_SPREAD_SHARE * dist:
        return {"skip": True}
    lot = spec["min_lot"]
    risk = (dist + spec.get("spread", 0)) * spec["value_per_lot"] * lot
    prof = abs(s["tp"] - s["entry"]) * spec["value_per_lot"] * lot
    return {"lot": lot, "risk_usd": risk, "profit_usd": prof}


def stars(score):
    v = round(score) / 2  # шаг 0.5 звезды: оценка 7.0 = 3.5 звезды
    full = int(v)
    return "⭐" * full + ("½" if v - full else "") + f" ({v:g}/5)"


# ---------------------------------------------------------------- новости
def skip_event(ev):
    t = ev["title"].lower()
    return any(w in t for w in ("election", "holiday", "daylight", "bank holiday"))


def load_news(now_u, force=False):
    global EVENTS
    st = STATE.setdefault("news", {})
    fresh = st.get("events") is not None and now_u.timestamp() - st.get("ts", 0) < 7200
    retry = now_u.timestamp() - st.get("fail", 0) < 600
    if OFFLINE_DIR or (not force and (fresh or retry)):
        EVENTS = _decode_events(st.get("events") or [])
        return
    raw = []
    ok = False
    urls = CALENDAR_URLS if now_u.weekday() >= 4 else CALENDAR_URLS[:1]
    for u in urls:
        try:
            raw += http_json(u, timeout=20)
            ok = True
        except Exception as e:
            print("календарь недоступен:", getattr(e, "code", e))
    if ok:
        evs = []
        for r in raw:
            if r.get("country") != "USD" or r.get("impact") not in ("High", "Medium"):
                continue
            try:
                dt = datetime.fromisoformat(r["date"]).astimezone(timezone.utc)
            except Exception:
                continue
            evs.append({"title": r.get("title", "?"), "dt": dt.isoformat(),
                        "impact": r["impact"], "forecast": r.get("forecast", ""),
                        "previous": r.get("previous", "")})
        st["events"], st["ts"] = evs, now_u.timestamp()
    else:
        st["fail"] = now_u.timestamp()
    EVENTS = _decode_events(st.get("events") or [])


def _decode_events(raw):
    out = []
    for e in raw:
        try:
            out.append({**e, "dt": datetime.fromisoformat(e["dt"])})
        except Exception:
            pass
    return sorted(out, key=lambda e: e["dt"])


def high_groups(now_u=None):
    g = {}
    for e in EVENTS:
        if e["impact"] == "High" and not skip_event(e):
            g.setdefault(e["dt"], []).append(e)
    return g


def news_blackout(now_u):
    """Заморозка новых входов вокруг High-новостей (или резервное окно)."""
    if not STATE.get("news", {}).get("events") and not EVENTS:
        return in_window(kyiv(now_u), *FALLBACK_NEWS_BLOCK)
    for dt in high_groups():
        m = (dt - now_u).total_seconds() / 60
        if -NEWS_AFTER <= m <= NEWS_BEFORE:
            return True
    return False


def near_news(now_u, before=70, after=100):
    for dt in high_groups():
        m = (dt - now_u).total_seconds() / 60
        if -after <= m <= before:
            return True
    return False


def ev_line(e):
    icon = "🔴" if e["impact"] == "High" else "🟠"
    extra = []
    if e.get("forecast"):
        extra.append(f"прогноз {esc(e['forecast'])}")
    if e.get("previous"):
        extra.append(f"пред. {esc(e['previous'])}")
    tail = f" ({', '.join(extra)})" if extra else ""
    return f"{icon} {hhmm(e['dt'])} {esc(e['title'])}{tail}"


def news_block(now_u, hours=24, past_min=60, with_help=False):
    lo, hi = now_u - timedelta(minutes=past_min), now_u + timedelta(hours=hours)
    evs = [e for e in EVENTS if lo <= e["dt"] <= hi]
    allx = [e for e in EVENTS if e["dt"] > now_u]
    if not evs:
        nxt = next((e for e in allx if e["impact"] == "High"), None)
        s = f"📅 Важных новостей США в ближайшие {hours} ч нет."
        if nxt:
            k = kyiv(nxt["dt"])
            s += f" Следующая: {k.strftime('%d.%m %H:%M')} {esc(nxt['title'])}."
        return s
    lines = [f"📅 <b>Новости США (время Киева)</b>"]
    day = None
    for e in evs:
        d = kyiv(e["dt"]).strftime("%d.%m")
        if d != day:
            day = d
            lines.append(f"<i>{d}</i>")
        lines.append(ev_line(e))
    if any("election" in e["title"].lower() for e in evs):
        lines.append("🗳 Выборы в Конгресс США: рынки в такие дни и ночью после них "
                     "двигаются нервнее, спреды шире. Входить только от уровней.")
    if with_help:
        lines.append("Как работает бот: за час предупредит, за 10 мин заморозит "
                     "входы, после выхода ждёт реакцию ≥2 ATR и ищет вход на откате (T5).")
    return "\n".join(lines)


def news_alerts(now_u):
    al = STATE.setdefault("alerts", {})
    for dt, evs in high_groups().items():
        m = (dt - now_u).total_seconds() / 60
        k = dt.strftime("%Y%m%d%H%M")
        names = "\n".join(ev_line(e) for e in evs)
        if 10 < m <= 62 and f"p60|{k}" not in al:
            al[f"p60|{k}"] = now_u.timestamp()
            send(f"📅 <b>Через ~{int(m)} мин — важные данные США ({hhmm(dt)} Киев)</b>\n"
                 f"{names}\n\n"
                 "Как играем: за 10 минут до выхода бот не даёт новых входов "
                 "(спред шире, скачок в обе стороны). Открытую позицию сократи или "
                 "переведи стоп в безубыток. Сильные данные обычно поддерживают "
                 "доллар (давят на золото и крипту), слабые наоборот, но первая "
                 "реакция часто ложная. После выхода я жду настоящий импульс "
                 "(≥2 ATR) и ищу вход на откате.")
        if 0 < m <= 10.5 and f"p10|{k}" not in al:
            al[f"p10|{k}"] = now_u.timestamp()
            al[f"p60|{k}"] = now_u.timestamp()
            send(f"⛔ <b>Через ~{max(1, int(m))} мин данные США ({hhmm(dt)} Киев)</b>\n"
                 f"{names}\nНовые входы заморожены до {hhmm(dt + timedelta(minutes=NEWS_AFTER))}. "
                 "После этого — T5 или ГОТОВЬСЯ.")


# ---------------------------------------------------------------- сообщения
def news_note(now_u):
    for dt, evs in sorted(high_groups().items()):
        m = (dt - now_u).total_seconds() / 60
        if 0 < m <= 180:
            return (f"📅 Через {int(m)} мин ({hhmm(dt)}) выходят данные США: "
                    f"{esc(evs[0]['title'])}. Если войдёшь, к выходу сократи позицию "
                    f"или перенеси стоп в безубыток.")
    return None


def msg_trade(sym, spec, s, sz, bar_close, now_u):
    arrow = "🟢 LONG (Buy по Ask)" if s["dir"] == "LONG" else "🔴 SHORT (Sell по Bid)"
    exp = bar_close + timedelta(minutes=10)
    lines = [
        f"{spec['icon']} <b>{spec['name']} · {sym}</b> — {arrow}",
        f"Тактика: {s['tactic']} · «{esc(s['level_name'])}» {fmt(s['level'])}",
        f"Вход: ~{fmt(s['entry'])}  (свеча M5 закрылась в {hhmm(bar_close)})",
        f"SL: {fmt(s['sl'])}  ·  TP: {fmt(s['tp'])}  (R:R {s['rr']:.1f})",
    ]
    ob = s.get("obstacle")
    if ob:
        lines.append(f"Препятствие по пути: «{ob[0]}» {fmt(ob[1])}, "
                     f"там можно зафиксировать часть.")
    lines += [
        f"На {sz['lot']} лота: стоп −${sz['risk_usd']:.2f}, цель +${sz['profit_usd']:.2f} "
        f"(объём решаешь сам)",
        f"Качество: {stars(s['score'])}",
        f"Действует до {hhmm(exp)} (Киев); если цена ушла дальше 0.3R от входа — пропускаем.",
        "Почему: " + "; ".join(s["reasons"] or ["свип уровня с возвратом"]),
        "Ведение: при +1R стоп в безубыток; закрытие M5 за уровень сетапа отменяет идею.",
    ]
    nn = news_note(now_u)
    if nn:
        lines.append(nn)
    lines.append(f"⚠️ Сверь цену и спред в MT5 ({spec['mt5']}).")
    return "\n".join(lines)


def msg_prep(sym, spec, p):
    if p.get("news"):
        d = "вверх" if p["dir"] == 1 else "вниз"
        act = "LONG" if p["dir"] == 1 else "SHORT"
        return (f"🟡 {spec['icon']} <b>{spec['name']}</b> — ГОТОВЬСЯ (после новости)\n"
                f"«{esc(p['title'])}» ({hhmm(p['t0'])}): импульс {d} {fmt(p['rng'])} "
                f"({p['k']:.1f}×ATR) до {fmt(p['ext'])}.\n"
                f"Жду откат в зону {fmt(p['zone'][0])}–{fmt(p['zone'][1])} (38–62% импульса) "
                f"и закрытие M5 по направлению импульса → {act}, SL за откатом, "
                f"цель — обновление экстремума.\n"
                f"Если цена уйдёт без отката — не догоняем.")
    if p["side"] == "low":
        plan = (f"Если прокол {fmt(p['level'])} и M5 закроется выше — готовим LONG. "
                f"Если пробой с закрытием ниже и ретест снизу — возможен SHORT.")
    else:
        plan = (f"Если прокол {fmt(p['level'])} и M5 закроется ниже — готовим SHORT. "
                f"Если пробой с закрытием выше и ретест — возможен LONG.")
    return (f"🟡 {spec['icon']} <b>{spec['name']}</b> — ГОТОВЬСЯ\n"
            f"Цена {fmt(p['price'])} рядом с «{esc(p['level_name'])}» {fmt(p['level'])}.\n"
            f"{plan}\nПоставь уведомление в MT5 на этот уровень.")


# ---------------------------------------------------------------- анализ по запросу
def snapshot(sym, now_u, max_age=90):
    spec = INSTRUMENTS[sym]
    m5 = get_bars(sym, "5min", 600, max_age)
    closed = closed_bars(m5, now_u, 5)
    if len(closed) < 80:
        raise RuntimeError("мало данных")
    ctx = build_ctx(closed, get_h1(sym), now_u)
    price = m5[-1]["c"]
    age = max(0.0, (now_u - (m5[-1]["t"] + timedelta(minutes=5))).total_seconds() / 60)
    levels = key_levels(closed, spec, price)
    above = sorted([l for l in levels if l[1] > price], key=lambda l: l[1] - price)
    below = sorted([l for l in levels if l[1] <= price], key=lambda l: price - l[1])
    setups = find_setups(sym, spec, closed, ctx) + news_setups(sym, spec, closed, ctx)
    return {"sym": sym, "spec": spec, "closed": closed, "ctx": ctx, "price": price,
            "age": age, "above": above, "below": below, "setups": setups,
            "a5": atr(closed, 14)}


def scenarios(snap):
    """Условные планы «что ждём»: ориентиры, реальный SL зависит от свипа."""
    p, a5, ctx = snap["price"], snap["a5"], snap["ctx"]
    lines = []
    levels = snap["above"] + snap["below"]
    if snap["below"]:
        nm, L, _ = snap["below"][0]
        entry, sl = L + 0.2 * a5, L - 0.8 * a5
        tp, _ = pick_target(levels, entry, entry - sl, "LONG")
        rr = abs(tp - entry) / abs(entry - sl)
        lines.append(f"• LONG: M5 проколет {fmt(L)} («{nm}») и закроется выше → "
                     f"вход ≈{fmt(entry)}, SL ≈{fmt(sl)}, цель {fmt(tp)} "
                     f"(R:R {'>5' if rr > 5 else f'{rr:.1f}'}, ориентир)")
    if snap["above"]:
        nm, L, _ = snap["above"][0]
        entry, sl = L - 0.2 * a5, L + 0.8 * a5
        tp, _ = pick_target(levels, entry, sl - entry, "SHORT")
        rr = abs(entry - tp) / abs(sl - entry)
        lines.append(f"• SHORT: M5 проколет {fmt(L)} («{nm}») и закроется ниже → "
                     f"вход ≈{fmt(entry)}, SL ≈{fmt(sl)}, цель {fmt(tp)} "
                     f"(R:R {'>5' if rr > 5 else f'{rr:.1f}'}, ориентир)")
    if ctx["h1"] == 1 and snap["above"]:
        lines.append(f"• По тренду H1 ↑: закрытие M5 выше {fmt(snap['above'][0][1])} "
                     f"и ретест сверху → LONG (T2).")
    if ctx["h1"] == -1 and snap["below"]:
        lines.append(f"• По тренду H1 ↓: закрытие M5 ниже {fmt(snap['below'][0][1])} "
                     f"и ретест снизу → SHORT (T2).")
    return lines


def render_full(snap, now_u):
    spec, ctx, p, a5 = snap["spec"], snap["ctx"], snap["price"], snap["a5"]
    a60 = ctx["a60"] or a5 * 3.4
    ar = {1: "↑", -1: "↓", 0: "→"}
    head = (f"{spec['icon']} <b>{spec['name'].upper()}</b> ({snap['sym']}) · "
            f"{hhmm(now_u)} Киев\nЦена {fmt(p)}")
    if snap["age"] > 20:
        head += f"  ⚠️ данные {int(snap['age'])} мин назад: рынок закрыт или нет котировок"
    lines = [head,
             f"Тренд: H1 {ar[ctx['h1']]} · H4 {ar[ctx['h4']]}   |   "
             f"ATR M5 {fmt(a5)}, ATR H1 {fmt(a60)}"]
    if ctx["day_ratio"] is not None:
        r = ctx["day_ratio"]
        tail = " — дневной ход почти исчерпан, продолжение тренда сложнее" if r >= 1.0 else ""
        lines.append(f"Ход дня: {r * 100:.0f}% от среднего дневного диапазона{tail}")
    if ctx["regime"] is not None and ctx["regime"] < 0.6:
        lines.append("Рынок вялый (ATR ниже суточной нормы): ходы короткие, спред важнее.")
    lines.append("")
    lines.append("<b>Ближайшие уровни</b>")
    for nm, L, _ in reversed(snap["above"][:3]):
        lines.append(f"↑ {fmt(L)}  {nm}  (+{fmt(L - p)}, {(L - p) / a60:.1f} ATR-H1)")
    lines.append(f"● сейчас {fmt(p)}")
    for nm, L, _ in snap["below"][:3]:
        lines.append(f"↓ {fmt(L)}  {nm}  (−{fmt(p - L)}, {(p - L) / a60:.1f} ATR-H1)")
    lines.append("")
    trades = [s for s in snap["setups"] if s["kind"] == "TRADE"]
    preps = [s for s in snap["setups"] if s["kind"] == "PREP"]
    sz_spec = spec
    if trades:
        s = trades[0]
        ok = s["score"] >= MIN_SCORE
        lines.append("🔥 <b>СЕЙЧАС ЕСТЬ СЕТАП</b>" if ok else
                     f"⚪ Есть слабый сетап ({stars(s['score'])}), ниже порога 3.5⭐: не берём.")
        sz = size(sz_spec, s)
        if sz and not sz.get("skip"):
            lines.append(msg_trade(snap["sym"], spec, s, sz,
                                   snap["closed"][-1]["t"] + timedelta(minutes=5), now_u))
        else:
            lines.append(f"{s['dir']} от {fmt(s['level'])}: спред съедает стоп, пропускаем.")
    elif preps:
        for pr in preps:
            lines.append(msg_prep(snap["sym"], spec, pr))
    else:
        lines.append("Сейчас входа нет: ликвидность не снята, цена между уровнями. "
                     "ГОТОВЬСЯ пришлю, когда цена подойдёт к уровню ближе 0.35 ATR-H1.")
    lines.append("")
    lines.append("<b>Что ждём</b>")
    lines += scenarios(snap) or ["нет данных для сценариев"]
    nb = [e for e in EVENTS if e["impact"] == "High" and not skip_event(e)
          and -30 <= (e["dt"] - now_u).total_seconds() / 60 <= 360]
    if nb:
        lines.append("")
        lines.append("📅 Ближайшие важные новости: " + "; ".join(
            f"{hhmm(e['dt'])} {esc(e['title'])}" for e in nb[:3]))
    lines.append("")
    lines.append(f"⚠️ Цены Twelve Data ≠ FxPro: сверяй цену и спред в MT5 ({spec['mt5']}).")
    return "\n".join(lines)


def render_line(snap):
    spec, ctx, p = snap["spec"], snap["ctx"], snap["price"]
    ar = {1: "↑", -1: "↓", 0: "→"}
    up = f"↑{fmt(snap['above'][0][1])}" if snap["above"] else "—"
    dn = f"↓{fmt(snap['below'][0][1])}" if snap["below"] else "—"
    tr = [s for s in snap["setups"] if s["kind"] == "TRADE" and s["score"] >= MIN_SCORE]
    pr = [s for s in snap["setups"] if s["kind"] == "PREP"]
    st = ("🔥 есть сетап" if tr else "🟡 готовься" if pr else "нет входа")
    old = " ⚠️ данные устарели" if snap["age"] > 20 else ""
    return (f"{spec['icon']} <b>{spec['name']}</b> {fmt(p)} · H1{ar[ctx['h1']]} H4{ar[ctx['h4']]} · "
            f"{up} / {dn} · {st}{old}")


def scan_all(now_u):
    lines = []
    for sym in INSTRUMENTS:
        try:
            lines.append(render_line(snapshot(sym, now_u, 120)))
        except Exception as e:
            lines.append(f"{INSTRUMENTS[sym]['icon']} {INSTRUMENTS[sym]['name']}: "
                         f"нет данных ({esc(e)})")
    return "\n".join(lines)


# ---------------------------------------------------------------- журнал
def parse_result(text):
    t = text.lower().replace("−", "-").replace("–", "-").replace(",", ".")
    tac = re.search(r"\bt(1[01]|[1-9])\b", t)
    tac = ("T" + tac.group(1)) if tac else "?"
    sym = next((v for k, v in ALIASES.items() if k in t), None)
    t2 = re.sub(r"\bt\d+\b", " ", t)
    m = re.search(r"[+-]?\d+(?:\.\d+)?", t2)
    if not m:
        return None
    r = float(m.group(0))
    neg = any(w in t2 for w in ("минус", "стоп", "loss", "лосс", "sl "))
    if neg and r > 0 and not m.group(0).startswith("+"):
        r = -r
    return {"ts": time.time(), "r": r, "tac": tac, "sym": sym}


def stats_text():
    j = STATE.get("journal", [])
    if not j:
        return ("Журнал пуст. После каждой сделки пиши: «итог +1.5» или «итог -1» "
                "(можно с тактикой: «итог T1 +1.5»). Через 20+ сделок посчитаю реальный винрейт.")
    n = len(j)
    wins = sum(1 for x in j if x["r"] > 0)
    tot = sum(x["r"] for x in j)
    lines = [f"📒 <b>Журнал: {n} сделок</b>",
             f"Винрейт {wins / n * 100:.0f}% · сумма {tot:+.2f}R · среднее {tot / n:+.2f}R на сделку"]
    by = {}
    for x in j:
        by.setdefault(x["tac"], []).append(x["r"])
    for k, v in sorted(by.items()):
        w = sum(1 for r in v if r > 0)
        lines.append(f"{k}: {len(v)} сд., винрейт {w / len(v) * 100:.0f}%, {sum(v):+.2f}R")
    if n < 20:
        lines.append(f"Данных мало ({n} из 20+): выводы пока ненадёжны.")
    return "\n".join(lines)


# ---------------------------------------------------------------- команды
HELP = (
    "<b>Команды бота v" + VERSION + "</b>\n"
    "/gold /btc /eth /spcx — разбор инструмента: тренд, уровни, что ждём\n"
    "/scan — коротко по всем инструментам\n"
    "/news — новости США на ближайшие сутки\n"
    "/calc gold 3885 3875 3910 0.05 — риск и прибыль в $ (инструмент, вход, SL, TP, лот)\n"
    "итог +1.5 или итог -1 — записать результат сделки (можно «итог T1 +1.5»)\n"
    "/stats — винрейт и R по журналу, /undo — удалить последнюю запись\n"
    "/status — состояние бота\n"
    "Можно писать и словами: «что по золоту», «новости», «статус».\n"
    "Сигналы и «ГОТОВЬСЯ» приходят сами. Объём входа всегда решаешь ты.")


def find_sym(text):
    return next((v for k, v in ALIASES.items() if k in text), None)


def route(text, now_u):
    low = (text or "").strip().lower()
    if not low:
        return None
    cmd, args = None, []
    if low.startswith("/"):
        parts = low.split()
        cmd, args = parts[0][1:].split("@")[0], parts[1:]
    elif low.startswith("итог") or low.startswith("result"):
        cmd, args = "itog", low.split()[1:]
    if cmd == "итог":
        cmd = "itog"
    if cmd in ("start", "help", "помощь") or (cmd is None and low in ("help", "помощь", "команды")):
        return HELP
    if cmd == "itog":
        r = parse_result(" ".join(args))
        if not r:
            return "Не вижу числа. Пример: итог +1.5 или итог -1 или итог T1 +1.5"
        STATE.setdefault("journal", []).append(r)
        j = STATE["journal"]
        w = sum(1 for x in j if x["r"] > 0)
        return (f"Записал: {r['r']:+g}R ({r['tac']}). Всего {len(j)}, винрейт "
                f"{w / len(j) * 100:.0f}%, сумма {sum(x['r'] for x in j):+.2f}R.")
    if cmd == "undo":
        j = STATE.get("journal", [])
        if not j:
            return "Журнал пуст."
        x = j.pop()
        return f"Удалил последнюю запись ({x['r']:+g}R)."
    if cmd == "stats" or (cmd is None and ("статистик" in low or low == "stats")):
        return stats_text()
    if cmd == "status" or (cmd is None and "статус" in low):
        return status_text(now_u)
    if cmd == "news" or (cmd is None and "новост" in low):
        return news_block(now_u, 48, 90, with_help=True)
    if cmd == "scan" or (cmd is None and (low in ("scan", "скан", "все", "всё") or "что там" in low)):
        return scan_all(now_u)
    if cmd == "calc":
        return calc_text(args)
    sym = find_sym(cmd if cmd else low)
    if sym:
        return render_full(snapshot(sym, now_u), now_u)
    return "Не понял. Напиши /help, там все команды."


def calc_text(args):
    sym = next((find_sym(a) for a in args if find_sym(a)), None)
    nums = []
    for a in args:
        try:
            nums.append(float(a.replace(",", ".")))
        except ValueError:
            pass
    if not sym or len(nums) < 3:
        return "Формат: /calc gold 3885 3875 3910 0.05 (инструмент, вход, SL, TP, лот)"
    spec = INSTRUMENTS[sym]
    entry, sl, tp = nums[:3]
    lot = nums[3] if len(nums) > 3 else spec["min_lot"]
    v = spec["value_per_lot"] * lot
    risk = abs(entry - sl) * v
    spread = spec["spread"] * v
    prof = abs(tp - entry) * v
    rr = abs(tp - entry) / abs(entry - sl) if entry != sl else 0
    d = "LONG" if tp > entry else "SHORT"
    warn = ""
    if (d == "LONG" and sl >= entry) or (d == "SHORT" and sl <= entry):
        warn = "\n⚠️ SL с неправильной стороны от входа."
    return (f"🧮 {spec['name']} {d}, {lot:g} лота\n"
            f"Стоп: −${risk:.2f} (+ спред ≈${spread:.2f})\nЦель: +${prof:.2f}\n"
            f"R:R {rr:.2f}. Спред = {spec['spread'] / abs(entry - sl) * 100 if entry != sl else 0:.0f}% стопа."
            f"{warn}\nКонтракт: {spec['value_per_lot']} на 1 лот (сверь с MT5).")


def status_text(now_u):
    a = api_counter()
    ages = []
    for sym in INSTRUMENTS:
        t = STATE.get("last_bar", {}).get(sym)
        ages.append(f"{INSTRUMENTS[sym]['name']}: {t[11:16] if t else '—'} UTC")
    ne = len(EVENTS)
    nts = STATE.get("news", {}).get("ts")
    return (f"✅ Бот v{VERSION} работает\nВремя Киев: {kyiv(now_u).strftime('%d.%m %H:%M')}\n"
            f"Последняя свеча M5 в анализе: " + "; ".join(ages) + "\n"
            f"Запросов Twelve Data сегодня: {a['n']}/800\n"
            f"Новости: {ne} событий" + (f", обновлено {hhmm(datetime.fromtimestamp(nts, timezone.utc))}"
                                         if nts else ", календарь не загружен") + "\n"
            f"Журнал: {len(STATE.get('journal', []))} сделок\n"
            f"Сигналы от 3.5⭐, R:R ≥ {MIN_R}.")


# ---------------------------------------------------------------- Telegram
def tg(method, params=None, timeout=20):
    data = urllib.parse.urlencode(params).encode() if params else None
    return http_json(f"https://api.telegram.org/bot{TG_TOKEN}/{method}",
                     data=data, timeout=timeout)


def send(text, chat=None):
    chat = chat or CHAT
    if DRY or not TG_TOKEN or not chat:
        print("---- (консоль) ----\n" + text + "\n")
        return
    chunks = [text[i:i + 3900] for i in range(0, len(text), 3900)] or [text]
    for ch in chunks:
        try:
            tg("sendMessage", {"chat_id": chat, "text": ch, "parse_mode": "HTML",
                               "disable_web_page_preview": "true"})
        except urllib.error.HTTPError as e:
            hint = {401: "неверный TG_TOKEN", 404: "неверный TG_TOKEN",
                    400: "неверный TG_CHAT или не нажат Start у бота"}.get(e.code, "")
            print("telegram ошибка:", e.code, hint)
            if e.code in (401, 404):
                return
            try:
                plain = html.unescape(re.sub(r"<[^>]+>", "", ch))
                tg("sendMessage", {"chat_id": chat, "text": plain})
            except Exception as e2:
                print("telegram ошибка:", getattr(e2, "code", e2))
        except Exception as e:
            print("telegram ошибка:", getattr(e, "code", e))


def resolve_chat():
    if TG_CHAT:
        return TG_CHAT
    if STATE.get("_chat"):
        return STATE["_chat"]
    if not TG_TOKEN:
        return None
    try:
        upd = tg("getUpdates").get("result", [])
    except Exception as e:
        print("getUpdates ошибка:", getattr(e, "code", e))
        return None
    for u in reversed(upd):
        cid = (u.get("message") or {}).get("chat", {}).get("id")
        if cid:
            STATE["_chat"] = str(cid)
            return STATE["_chat"]
    return None


def register_commands():
    cmds = [("gold", "Разбор золота"), ("btc", "Разбор биткоина"),
            ("eth", "Разбор эфира"), ("spcx", "Разбор SpaceX"),
            ("scan", "Коротко по всем"), ("news", "Новости США"),
            ("stats", "Журнал сделок"), ("status", "Состояние бота"),
            ("help", "Все команды")]
    try:
        tg("setMyCommands", {"commands": json.dumps(
            [{"command": c, "description": d} for c, d in cmds])})
    except Exception as e:
        print("setMyCommands:", getattr(e, "code", e))


def handle_message(msg, now_u):
    cid = str((msg.get("chat") or {}).get("id", ""))
    if CHAT and cid != str(CHAT):
        return
    if now_u.timestamp() - msg.get("date", 0) > 1800:
        return  # слишком старое, не отвечаем
    text = msg.get("text", "")
    try:
        reply = route(text, now_u)
    except Exception as e:
        print("команда упала:", e)
        reply = f"Не получилось выполнить: {esc(e)}. Попробуй ещё раз через минуту."
    if reply:
        send(reply, cid)


def poll(timeout):
    params = {"timeout": int(timeout), "allowed_updates": json.dumps(["message"])}
    if STATE.get("offset"):
        params["offset"] = STATE["offset"]
    try:
        res = tg("getUpdates", params, timeout=timeout + 15)
    except Exception as e:
        print("getUpdates:", getattr(e, "code", e))
        time.sleep(min(5, max(1, timeout)))
        return
    for u in res.get("result", []):
        STATE["offset"] = u["update_id"] + 1
        if u.get("message"):
            handle_message(u["message"], datetime.now(timezone.utc))


# ---------------------------------------------------------------- сканирование
def market_open(spec, now_u):
    now_k = kyiv(now_u)
    if OFFLINE_DIR:
        return True
    if spec.get("weekdays_only") and now_k.weekday() >= 5:
        return False
    if spec["sessions"] is not None:
        if any(in_window(now_k, (a, 0), (b, 0)) for a, b in spec["sessions"]):
            return True
        return near_news(now_u)  # около важной новости смотрим и вне окон
    return True


def process(sym, spec, snap, now_u, bar_close):
    """Фильтры и отправка найденных сетапов."""
    now_k = kyiv(now_u)
    blocked = news_blackout(now_u) or (
        spec.get("rollover") and in_window(now_k, *ROLLOVER))
    sig = STATE.setdefault("sig", {})
    day = now_k.strftime("%Y%m%d")
    dc = STATE.setdefault("daycnt", {})
    if dc.get("day") != day:
        dc.clear()
        dc["day"] = day
    last_trade = STATE.setdefault("last_trade", {}).get(sym, 0)
    sent = 0
    for s in snap["setups"]:
        if s.get("news"):
            key = f"{sym}|NP|{s['key']}"
        else:
            key = f"{sym}|{s['kind']}|{s.get('level_name')}|{round(s['level'], 2)}"
        cooldown = 120 if s.get("news") else 90 if s["kind"] == "PREP" else 45
        last = sig.get(key)
        if last and now_u.timestamp() - last < cooldown * 60:
            continue
        if s["kind"] == "TRADE":
            if blocked or s["score"] < MIN_SCORE:
                continue
            if dc.get(f"{sym}|T", 0) >= MAX_TRADES_DAY or \
                    now_u.timestamp() - last_trade < TRADE_PAUSE_MIN * 60:
                continue  # дисциплина: без потока сигналов
            risk = abs(s["entry"] - s["sl"])
            drift = (snap["price"] - s["entry"]) * (1 if s["dir"] == "LONG" else -1)
            if drift > 0.3 * risk or drift < -0.5 * risk:
                continue  # цена уже ушла от входа
            sz = size(spec, s)
            if not sz or sz.get("skip"):
                continue
            send(msg_trade(sym, spec, s, sz, bar_close, now_u))
            dc[f"{sym}|T"] = dc.get(f"{sym}|T", 0) + 1
            STATE["last_trade"][sym] = now_u.timestamp()
        else:
            if blocked and not s.get("news"):
                continue
            if dc.get(f"{sym}|P", 0) >= MAX_PREPS_DAY or \
                    now_u.timestamp() - last_trade < TRADE_PAUSE_MIN * 60:
                continue
            send(msg_prep(sym, spec, s))
            dc[f"{sym}|P"] = dc.get(f"{sym}|P", 0) + 1
        sig[key] = now_u.timestamp()
        sent += 1
    return sent


def scan(sym, spec, now_u):
    try:
        m5 = get_bars(sym, "5min", 600, 0)
        expected = datetime.fromtimestamp(
            now_u.timestamp() // 300 * 300 - 300, timezone.utc)
        tries = 0
        while not OFFLINE_DIR and tries < 3 and \
                closed_bars(m5, now_u, 5)[-1:] and \
                closed_bars(m5, now_u, 5)[-1]["t"] < expected:
            time.sleep(10)  # провайдер ещё не отдал закрытую свечу
            m5 = get_bars(sym, "5min", 600, 0)
            tries += 1
        closed = closed_bars(m5, now_u, 5)
        if len(closed) < 80:
            print(sym, "мало данных")
            return 0
        if not OFFLINE_DIR and now_u - (closed[-1]["t"] + timedelta(minutes=5)) > timedelta(minutes=25):
            print(sym, "данные устарели, рынок закрыт?")
            return 0
        bar_id = closed[-1]["t"].isoformat()
        lb = STATE.setdefault("last_bar", {})
        if lb.get(sym) == bar_id:
            return 0
        lb[sym] = bar_id
        ctx = build_ctx(closed, get_h1(sym), now_u)
        snap = {"price": m5[-1]["c"], "setups":
                find_setups(sym, spec, closed, ctx) + news_setups(sym, spec, closed, ctx)}
        n = process(sym, spec, snap, now_u, closed[-1]["t"] + timedelta(minutes=5))
        print(f"{sym}: свеча {bar_id[11:16]} UTC, сетапов найдено {len(snap['setups'])}, отправлено {n}")
        return n
    except Exception as e:
        print(sym, "ошибка:", getattr(e, "code", e) if isinstance(e, urllib.error.HTTPError) else e)
        return 0


def tick(now_u):
    sent = 0
    load_news(now_u)
    news_alerts(now_u)
    for sym, spec in INSTRUMENTS.items():
        if not market_open(spec, now_u):
            continue
        step = spec["every_min"] * 60
        slot = int(now_u.timestamp() // step)
        if LAST_SLOT.get(sym) == slot:
            continue
        if now_u.timestamp() - slot * step < SCAN_DELAY:
            continue
        LAST_SLOT[sym] = slot
        sent += scan(sym, spec, now_u)
    briefs(now_u)
    return sent


def briefs(now_u):
    now_k = kyiv(now_u)
    if now_k.weekday() >= 5:
        return
    hm = (now_k.hour, now_k.minute)
    slot = None
    if (8, 55) <= hm < (9, 10):
        slot, title = "am", "☀️ <b>План на день</b>"
    elif (14, 55) <= hm < (15, 10):
        slot, title = "pm", "🌤 <b>План перед американской сессией</b>"
    if not slot:
        return
    key = f"{now_k.strftime('%Y%m%d')}|{slot}"
    b = STATE.setdefault("briefs", {})
    if key in b:
        return
    b[key] = now_u.timestamp()
    send(title + "\n" + scan_all(now_u) + "\n\n" + news_block(now_u, 12, 0)
         + "\n\nПодробно по любому инструменту: /gold /btc /eth /spcx")


def next_wake(now_u):
    t = now_u.timestamp()
    best = 25.0
    for spec in INSTRUMENTS.values():
        step = spec["every_min"] * 60
        best = min(best, max(1.0, (t // step + 1) * step + SCAN_DELAY - t))
    return best


def save_state():
    try:
        now = time.time()
        for k in ("sig", "alerts"):
            d = STATE.get(k, {})
            STATE[k] = {a: v for a, v in d.items() if now - v < 3 * 86400}
        STATE["briefs"] = {a: v for a, v in STATE.get("briefs", {}).items()
                           if now - v < 3 * 86400}
        json.dump(STATE, open(STATE_FILE, "w"))
    except Exception as e:
        print("не удалось сохранить состояние:", e)


def main():
    global CHAT, STATE
    try:
        STATE = json.load(open(STATE_FILE))
    except Exception:
        STATE = {}
    if STATE.get("v") != 2:  # старая память v1: оставляем только чат
        STATE = {"v": 2, "_chat": STATE.get("_chat")}
    CHAT = resolve_chat()
    have_tg = bool(TG_TOKEN) and not DRY
    if have_tg:
        register_commands()
        if CHAT and not STATE.get("hello_v2"):
            STATE["hello_v2"] = 1
            send(f"✅ Бот v{VERSION} запущен. Теперь я понимаю команды: /help.\n"
                 "Пиши «золото», «биток», «новости» или /scan, отвечу за секунды.")
    start = time.time()
    deadline = start + RUN_SECONDS
    last_save = start
    sent = 0
    print(f"старт v{VERSION}, работаем {RUN_SECONDS} сек")
    while time.time() < deadline:
        now_u = datetime.now(timezone.utc)
        try:
            sent += tick(now_u)
        except Exception as e:
            print("tick упал:", e)
        if have_tg and not CHAT:
            CHAT = resolve_chat()
        wake = min(next_wake(datetime.now(timezone.utc)), max(1.0, deadline - time.time()))
        if have_tg and CHAT:
            poll(wake)
        else:
            time.sleep(min(wake, 5) if DRY else wake)
        if time.time() - last_save > 60:
            save_state()
            last_save = time.time()
    save_state()
    print("сообщений отправлено:", sent)


if __name__ == "__main__":
    main()
