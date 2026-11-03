"""
Сканер сигналов для ручной торговли (FxPro MT5) -> Telegram.
Работает в GitHub Actions по расписанию, ПК не нужен.

Логика (без угадывания):
  T1  Свип ликвидности: прокол уровня (хай/лой прошлого дня, Азии, свинга)
      + закрытие M5 обратно за уровень + слом мини-структуры.
  T2  Пробой и ретест по тренду H1.
  PREP «Готовься»: цена подошла к ключевому уровню, сетап может
      сформироваться в ближайшие 15–30 минут.

Данные: Twelve Data REST (бесплатный ключ). Цены не равны FxPro —
бот всегда напоминает сверить цену и спред в MT5.
"""
import json
import math
import os
import sys
import time
from datetime import datetime, timedelta, timezone

import urllib.parse
import urllib.request

# ---------------------------------------------------------------- настройки
TWELVE_KEY = os.environ.get("TWELVE_KEY", "")
TG_TOKEN = os.environ.get("TG_TOKEN", "")
TG_CHAT = os.environ.get("TG_CHAT", "")
STATE_FILE = os.environ.get("STATE_FILE", "state.json")
OFFLINE_DIR = os.environ.get("OFFLINE_DIR", "")  # для тестов: csv вместо API
KYIV = timezone(timedelta(hours=2))  # зима; летом поставь 3

# value_per_lot = сколько $ даёт движение цены на 1.00 при объёме 1.00 лот.
# ПРОВЕРЬ в MT5: Market Watch -> символ -> Спецификация (Contract size).
INSTRUMENTS = {
    # spread = типичный спред FxPro в цене (со скриншотов MT5, ночь 03.11.2026).
    "XAU/USD": {"mt5": "GOLD", "value_per_lot": 100, "min_lot": 0.01,
                "step": 0.01, "spread": 0.15, "every_min": 5,
                "sessions": [(9, 13), (15, 19)]},
    "BTC/USD": {"mt5": "BITCOIN", "value_per_lot": 1, "min_lot": 0.01,
                "step": 0.01, "spread": 15.4, "every_min": 10, "sessions": None},
    "ETH/USD": {"mt5": "ETHEREUM", "value_per_lot": 1, "min_lot": 0.1,
                "step": 0.1, "spread": 3.0, "every_min": 10, "sessions": None},
    "SPCX":    {"mt5": "SPCX.O", "value_per_lot": 1, "min_lot": 1,
                "step": 1, "spread": 0.47, "every_min": 10,
                "sessions": [(16, 23)], "weekdays_only": True},
    # SOLANA отключена: спред ~0.75 при цене ~91 (0.8%) съедает почти весь стоп.
    # "SOL/USD": {"mt5": "SOLANA", "value_per_lot": 1, "min_lot": 1,
    #             "step": 1, "spread": 0.75, "every_min": 15, "sessions": None},
}
MAX_SPREAD_SHARE = 0.15  # спред не больше 15% стопа

# Окна, когда новые сигналы не даём (Киев): ролловер и выход US-данных.
BLOCK_WINDOWS = [((23, 30), (1, 30)), ((15, 25), (15, 45))]

MIN_R = 1.5
MIN_SCORE = 7.0  # = 3.5 звезды из 5


# ---------------------------------------------------------------- утилиты
def http_get(url, params):
    q = urllib.parse.urlencode(params)
    with urllib.request.urlopen(f"{url}?{q}", timeout=20) as r:
        return json.loads(r.read().decode())


def fetch_m5(symbol, n=300):
    """Возвращает список баров (старые -> новые): dict(t, o, h, l, c)."""
    if OFFLINE_DIR:
        fn = os.path.join(OFFLINE_DIR, symbol.replace("/", "") + ".csv")
        rows = [ln.strip().split(";") for ln in open(fn) if ln[0].isdigit()]
        data = [{"datetime": r[0], "open": r[1], "high": r[2],
                 "low": r[3], "close": r[4]} for r in rows]
    else:
        js = http_get("https://api.twelvedata.com/time_series", {
            "symbol": symbol, "interval": "5min", "outputsize": n,
            "timezone": "UTC", "apikey": TWELVE_KEY})
        if js.get("status") == "error":
            raise RuntimeError(js.get("message"))
        data = js["values"]
    bars = []
    for v in reversed(data):
        bars.append({
            "t": datetime.strptime(v["datetime"], "%Y-%m-%d %H:%M:%S")
                 .replace(tzinfo=timezone.utc),
            "o": float(v["open"]), "h": float(v["high"]),
            "l": float(v["low"]), "c": float(v["close"])})
    return bars


def resample(bars, minutes):
    out, cur = [], None
    for b in bars:
        key = b["t"].replace(minute=(b["t"].minute // minutes) * minutes,
                             second=0) if minutes < 60 else \
            b["t"].replace(minute=0, second=0)
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
        p = bars[i - 1]["c"]
        b = bars[i]
        trs.append(max(b["h"] - b["l"], abs(b["h"] - p), abs(b["l"] - p)))
    trs = trs[-n:]
    return sum(trs) / len(trs) if trs else 0.0


def ema(vals, n):
    k = 2 / (n + 1)
    e = vals[0]
    for v in vals[1:]:
        e = v * k + e * (1 - k)
    return e


def in_window(now_k, start, end):
    m = now_k.hour * 60 + now_k.minute
    s = start[0] * 60 + start[1]
    e = end[0] * 60 + end[1]
    return s <= m < e if s < e else (m >= s or m < e)


def fmt(x):
    return f"{x:,.2f}".replace(",", " ")


# ---------------------------------------------------------------- уровни
def key_levels(bars):
    """Хай/лой прошлого дня (UTC), Азии (00-07 UTC сегодня), свинги."""
    last = bars[-1]["t"]
    today = last.date()
    yday = [b for b in bars if b["t"].date() == today - timedelta(days=1)]
    asia = [b for b in bars if b["t"].date() == today and b["t"].hour < 7]
    lv = []
    if yday:
        lv += [("хай вчера", max(b["h"] for b in yday), "high"),
               ("лой вчера", min(b["l"] for b in yday), "low")]
    if asia and last.hour >= 7:
        lv += [("хай Азии", max(b["h"] for b in asia), "high"),
               ("лой Азии", min(b["l"] for b in asia), "low")]
    window = bars[-60:-6]  # последние ~5 часов, без свежих баров
    if window:
        lv += [("свинг-хай 5ч", max(b["h"] for b in window), "high"),
               ("свинг-лой 5ч", min(b["l"] for b in window), "low")]
    return lv


def h1_trend(bars):
    h1 = resample(bars, 60)
    if len(h1) < 25:
        return 0
    closes = [b["c"] for b in h1]
    e_now, e_prev = ema(closes[-50:], 20), ema(closes[-53:-3], 20)
    if closes[-1] > e_now and e_now > e_prev:
        return 1
    if closes[-1] < e_now and e_now < e_prev:
        return -1
    return 0


# ---------------------------------------------------------------- сетапы
def find_setups(symbol, bars):
    out = []
    if len(bars) < 80:
        return out
    a5 = atr(bars[:-1], 14)
    h1 = resample(bars, 60)
    a60 = atr(h1, 14)
    trend = h1_trend(bars)
    levels = key_levels(bars[:-1])
    b, prev = bars[-2], bars[-3]  # b = последний ЗАКРЫТЫЙ бар
    recent = bars[-8:-2]

    rng = b["h"] - b["l"]
    spike = rng > 4.5 * a5  # новостной спайк — не торгуем
    for name, lvl, side in levels:
        if spike:
            break
        # ---- T1 свип: прокол и закрытие обратно (+ обязательный слом M5)
        upper = rng and (b["c"] - b["l"]) / rng >= 0.6
        lower = rng and (b["h"] - b["c"]) / rng >= 0.6
        if side == "low" and b["l"] < lvl - 0.05 * a5 and b["c"] > lvl and upper \
                and b["c"] > max(x["h"] for x in bars[-5:-2]):
            mss = True
            entry, sl = b["c"], b["l"] - 0.15 * a5
            tgt = [l for n_, l, s in levels if s == "high" and l > entry]
            tp = min(tgt) if tgt else entry + 2 * (entry - sl)
            if "свинг" not in name or trend == 1:
                out.append(make("T1 свип", "LONG", name, lvl, entry, sl, tp,
                                mss, trend == 1, trend == -1))
        if side == "high" and b["h"] > lvl + 0.05 * a5 and b["c"] < lvl and lower \
                and b["c"] < min(x["l"] for x in bars[-5:-2]):
            mss = True
            entry, sl = b["c"], b["h"] + 0.15 * a5
            tgt = [l for n_, l, s in levels if s == "low" and l < entry]
            tp = max(tgt) if tgt else entry - 2 * (sl - entry)
            if "свинг" not in name or trend == -1:
                out.append(make("T1 свип", "SHORT", name, lvl, entry, sl, tp,
                                mss, trend == -1, trend == 1))

        # ---- T2 пробой + ретест по тренду H1
        broke_up = any(x["c"] > lvl for x in recent) and \
            min(x["l"] for x in bars[-20:-8]) < lvl
        if side == "high" and trend == 1 and broke_up and \
                b["l"] <= lvl + 0.2 * a5 and b["c"] > lvl and b["c"] > b["o"]:
            entry, sl = b["c"], min(b["l"], prev["l"]) - 0.2 * a5
            out.append(make("T2 ретест", "LONG", name, lvl, entry, sl,
                            entry + 2 * (entry - sl), True, True, False))
        broke_dn = any(x["c"] < lvl for x in recent) and \
            max(x["h"] for x in bars[-20:-8]) > lvl
        if side == "low" and trend == -1 and broke_dn and \
                b["h"] >= lvl - 0.2 * a5 and b["c"] < lvl and b["c"] < b["o"]:
            entry, sl = b["c"], max(b["h"], prev["h"]) + 0.2 * a5
            out.append(make("T2 ретест", "SHORT", name, lvl, entry, sl,
                            entry - 2 * (sl - entry), True, True, False))

        # ---- PREP: цена близко к уровню, свипа ещё нет
        dist = abs(b["c"] - lvl)
        untouched = (side == "low" and min(x["l"] for x in bars[-6:-1]) > lvl) \
            or (side == "high" and max(x["h"] for x in bars[-6:-1]) < lvl)
        if untouched and dist < 0.35 * a60:
            out.append({"kind": "PREP", "level_name": name, "level": lvl,
                        "side": side, "price": b["c"], "atr60": a60})
    # одна сделка на направление (берём с лучшей оценкой), один PREP на сторону
    best, preps = {}, {}
    for s in out:
        if s["kind"] == "TRADE":
            k = s["dir"]
            if k not in best or s["score"] > best[k]["score"]:
                best[k] = s
        else:
            k = s["side"]
            if k not in preps or abs(s["price"] - s["level"]) < \
                    abs(preps[k]["price"] - preps[k]["level"]):
                preps[k] = s
    if len(best) == 2:  # сигналы в обе стороны = неясно, ничего не даём
        best = {}
    return list(best.values()) + ([] if best else list(preps.values()))


def make(tac, d, lname, lvl, entry, sl, tp, mss, with_trend, against):
    risk = abs(entry - sl)
    reward = abs(tp - entry)
    rr = reward / risk if risk else 0
    score = 6.5
    reasons = []
    if mss:
        score += 1.0
        reasons.append("структура M5 сломалась в сторону сделки")
    if with_trend:
        score += 0.75
        reasons.append("по тренду H1")
    if against:
        score -= 0.5
        reasons.append("против тренда H1 (минус к оценке)")
    if "вчера" in lname or "Азии" in lname:
        score += 0.5
        reasons.append(f"снята ликвидность за сильным уровнем ({lname})")
    if rr >= 2:
        score += 0.5
    if rr < MIN_R:
        score -= 1.5
    return {"kind": "TRADE", "tactic": tac, "dir": d, "level_name": lname,
            "level": lvl, "entry": entry, "sl": sl, "tp": tp, "rr": rr,
            "score": round(min(score, 10), 1), "reasons": reasons}


# ---------------------------------------------------------------- риск
def size(spec, s):
    """Только справка: сколько $ риска/профита на минимальный лот. Объём решает трейдер."""
    dist = abs(s["entry"] - s["sl"])
    if spec.get("spread", 0) > MAX_SPREAD_SHARE * dist:
        return {"skip": True}
    lot = spec["min_lot"]
    risk = (dist + spec.get("spread", 0)) * spec["value_per_lot"] * lot
    prof = abs(s["tp"] - s["entry"]) * spec["value_per_lot"] * lot
    return {"lot": lot, "risk_usd": risk, "profit_usd": prof}


# ---------------------------------------------------------------- telegram
def send(text):
    if not TG_TOKEN:
        print("---- (нет TG_TOKEN, вывод в консоль) ----\n" + text)
        return
    data = urllib.parse.urlencode({"chat_id": TG_CHAT, "text": text,
                                   "parse_mode": "HTML",
                                   "disable_web_page_preview": "true"}).encode()
    urllib.request.urlopen(
        f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage", data, timeout=20)


def stars(score):
    v = round(score / 2 * 2) / 2  # шаг 0.5 звезды
    full = int(v)
    return "⭐" * full + ("½" if v - full else "") + f" ({v:g}/5)"


def msg_trade(sym, spec, s, sz):
    arrow = "🟢 LONG (Buy по Ask)" if s["dir"] == "LONG" else "🔴 SHORT (Sell по Bid)"
    exp = (datetime.now(KYIV) + timedelta(minutes=10)).strftime("%H:%M")
    lines = [
        f"<b>{sym}</b> — {arrow}",
        f"Тактика: {s['tactic']} от уровня «{s['level_name']}» {fmt(s['level'])}",
        f"Вход: ~{fmt(s['entry'])}",
        f"SL: {fmt(s['sl'])}",
        f"TP: {fmt(s['tp'])}  (R:R {s['rr']:.1f})",
        f"На {sz['lot']} лота: стоп −${sz['risk_usd']:.2f}, цель +${sz['profit_usd']:.2f} "
        f"(объём решаешь сам)",
        f"Качество: {stars(s['score'])}",
        f"Действует до: {exp} (Киев). Если цена ушла дальше 0.3R — пропускаем.",
        "Почему: " + "; ".join(s["reasons"] or ["свип уровня с возвратом"]),
        f"⚠️ Сверь цену/спред в MT5 ({spec['mt5']}) и новости перед входом.",
    ]
    return "\n".join(lines)


def msg_prep(sym, p):
    if p["side"] == "low":
        plan = (f"Если прокол {fmt(p['level'])} и M5 закроется выше — готовим LONG. "
                f"Если пробой с закрытием ниже и ретест снизу — возможен SHORT.")
    else:
        plan = (f"Если прокол {fmt(p['level'])} и M5 закроется ниже — готовим SHORT. "
                f"Если пробой с закрытием выше и ретест — возможен LONG.")
    return (f"🟡 <b>{sym}</b> — ГОТОВЬСЯ\n"
            f"Цена {fmt(p['price'])} рядом с уровнем «{p['level_name']}» "
            f"{fmt(p['level'])}.\n{plan}\nПоставь уведомление в MT5 на этот уровень.")


# ---------------------------------------------------------------- main
def due(spec, now_u, now_k):
    if OFFLINE_DIR:
        return True
    if spec.get("weekdays_only") and now_k.weekday() >= 5:
        return False
    if spec["sessions"] is not None:
        if now_k.weekday() >= 5 or not any(
                in_window(now_k, (a, 0), (b, 0)) for a, b in spec["sessions"]):
            return False
    return (now_u.minute % spec["every_min"]) < 5


def main():
    now_u = datetime.now(timezone.utc)
    now_k = now_u.astimezone(KYIV)
    blocked = any(in_window(now_k, s, e) for s, e in BLOCK_WINDOWS)
    try:
        state = json.load(open(STATE_FILE))
    except Exception:
        state = {}
    sent = 0
    for sym, spec in INSTRUMENTS.items():
        if not due(spec, now_u, now_k):
            continue
        try:
            bars = fetch_m5(sym)
        except Exception as e:
            print(sym, "ошибка данных:", e)
            continue
        if not OFFLINE_DIR and (now_u - bars[-1]["t"]) > timedelta(minutes=20):
            print(sym, "данные устарели, рынок закрыт?")
            continue
        for s in find_setups(sym, bars):
            key = f"{sym}|{s['kind']}|{s.get('level_name')}|{round(s['level'], 2)}"
            last = state.get(key)
            cooldown = 90 if s["kind"] == "PREP" else 45
            if last and (now_u.timestamp() - last) < cooldown * 60:
                continue
            if s["kind"] == "TRADE":
                if blocked or s["score"] < MIN_SCORE:
                    continue
                sz = size(spec, s)
                if not sz or sz.get("skip"):
                    continue
                send(msg_trade(sym, spec, s, sz))
            else:
                if blocked:
                    continue
                send(msg_prep(sym, s))
            state[key] = now_u.timestamp()
            sent += 1
        time.sleep(8)  # бесплатный тариф: 8 запросов в минуту
    # чистим старые ключи
    state = {k: v for k, v in state.items() if now_u.timestamp() - v < 86400}
    json.dump(state, open(STATE_FILE, "w"))
    print("сообщений отправлено:", sent)


if __name__ == "__main__":
    main()
