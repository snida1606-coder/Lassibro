#owner and Develpor @Mrbeaxt_trader 

from __future__ import annotations

import json
import re
import threading
import time
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from typing import Any, Callable
from urllib.parse import urlencode

import requests

FF_WEEK_URLS = (
    "https://nfs.faireconomy.media/ff_calendar_thisweek.json",
    "https://cdn-nfs.faireconomy.media/ff_calendar_thisweek.json",
)
FF_WEEK_URL = FF_WEEK_URLS[0]
_RSS_FEEDS = (
    "https://www.dailyforex.com/rss/forex-news",
    "https://www.fxstreet.com/rss",
)

_calendar_cache: dict[str, Any] = {"ts": 0.0, "data": None}
_CALENDAR_CACHE_SECS = 300  
_rss_cache: dict[str, Any] = {"ts": 0.0, "items": []}
_RSS_CACHE_SECS = 600

NEWS_GLOBAL_PAIRS: tuple[str, ...] = (
    "EUR/USD", "GBP/USD", "USD/JPY", "USD/CHF", "AUD/USD", "USD/CAD", "NZD/USD",
    "EUR/GBP", "EUR/JPY", "EUR/CHF", "EUR/AUD", "EUR/CAD", "EUR/NZD",
    "GBP/JPY", "GBP/CHF", "GBP/AUD", "GBP/CAD", "GBP/NZD",
    "AUD/JPY", "AUD/CHF", "AUD/CAD", "AUD/NZD",
    "CAD/JPY", "CAD/CHF", "CHF/JPY",
    "NZD/JPY", "NZD/CHF", "NZD/CAD",
    "XAU/USD",
)

NEWS_PAIRS_PER_PAGE = 8
NEWS_FILTERS = ("all", "high", "medium", "low")
NEWS_DAYS = (1, 2, 3)

_CURRENCY_FLAGS = {
    "USD": "🇺🇸", "EUR": "🇪🇺", "GBP": "🇬🇧", "JPY": "🇯🇵",
    "CHF": "🇨🇭", "CAD": "🇨🇦", "AUD": "🇦🇺", "NZD": "🇳🇿",
    "XAU": "🏅", "CNY": "🇨🇳",
}

_FF_COUNTRY_TO_CCY = {
    "USD": "USD", "EUR": "EUR", "GBP": "GBP", "JPY": "JPY",
    "CAD": "CAD", "AUD": "AUD", "NZD": "NZD", "CHF": "CHF",
    "CNY": "CNY", "CNH": "CNY",
}

_NEGATIVE_IF_HIGHER = (
    "unemployment", "jobless", "claims", "inventories", "inventory",
    "deficit", "debt", "continuing claims", "initial claims",
)

_MIN_REL_GAP = 0.015
_TIER_A_KEYWORDS = (
    "non-farm", "nonfarm", "nfp", "payroll",
    "cpi", "consumer price", "pce", "core pce",
    "fomc", "interest rate decision", "rate decision",
    "federal funds", "ecb rate", "boe rate", "boj rate", "rba rate", "boc rate",
    "gdp", "retail sales", "unemployment rate", "jobless rate",
)
_TIER_B_KEYWORDS = (
    "ppi", "producer price", "ism", "pmi", "employment change",
    "average hourly", "jolts", "confidence", "sentiment",
)

_PRENEWS_SKIP_KEYWORDS = (
    "industrial production", "manufacturing production",
    "trade balance", "current account", "zew", "ifo",
    "factory orders", "building permits", "housing starts",
)

_SPEECH_KEYWORDS = ("speech", "speaks", "testimony", "press conference", "minutes")

_BULLISH_HEADLINE = (
    "surge", "surges", "soar", "soars", "rally", "rallies", "jumps", "jump",
    "beats", "beat expectations", "stronger", "hawkish", "growth", "rebound",
    "optimism", "higher than expected", "above forecast", "hotter",
)
_BEARISH_HEADLINE = (
    "slump", "slumps", "plunge", "plunges", "falls", "fall", "drop", "drops",
    "misses", "miss expectations", "weaker", "dovish", "recession", "slowdown",
    "pessimism", "lower than expected", "below forecast", "cooler", "contraction",
)

NEWS_EMOJI_IDS = {

    "fire": 6264785189394717307,
    "calendar": 6102906733842144545,
    "clock": 5215484787325676090,
    "alarm": 5215484787325676090,
    "timer": 5382194935057372936,
    "trend_up": 6102644427304478726,
    "trend_down": 6102805248059906486,
    "up_arr": 6102644427304478726,
    "down_arr": 6102805248059906486,
    "list": 5258477770735885832,
    "refresh": 4956371914323920049,
    "robot": 5417909469319272937,
    "rocket": 6068700050928704109,
    "bolt": 5438571934210082705,
    "warn": 6276132901012640832,
    "writing": 5193004760994685438,
    "news": 5971837723676249096,
    "surprise": 6273865673676428425,
    "brain": 4958937938239947673,
    "check": 6267291337171670780,
    "crown": 6147893428186258508,
    "money": 6104726047628990417,
}

_gemini_lock = threading.Lock()
_gemini_idx = 0


def default_news_draft() -> dict:
    return {
        "pairs": list(NEWS_GLOBAL_PAIRS),
        "n_days": 1,
        "filter": "all",
        "page": 0,
        "ai_mode": True,
    }


def _u16len(s: str) -> int:
    return sum(2 if ord(c) > 0xFFFF else 1 for c in s)


def slash_pair(symbol: str) -> str:
    s = (symbol or "").strip().upper().replace(" ", "").replace("-", "").replace("_", "")
    if "/" in (symbol or ""):
        return symbol.strip().upper()
    for a in ("XAU", "XAG", "EUR", "GBP", "AUD", "NZD", "USD", "CAD", "CHF", "JPY"):
        if s.startswith(a) and len(s) > len(a):
            return f"{a}/{s[len(a):]}"
    if len(s) == 6:
        return f"{s[:3]}/{s[3:]}"
    return symbol.strip().upper()


def currencies_from_pairs(pairs: list[str] | tuple[str, ...]) -> set[str]:
    out: set[str] = set()
    for p in pairs:
        sp = slash_pair(p)
        if "/" in sp:
            a, b = sp.split("/", 1)
            out.add(a)
            out.add(b)
    return out


def fetch_ff_calendar(*, timeout: int = 40, retries: int = 4, force: bool = False) -> list[dict]:
   
    now = time.time()
    if (
        not force
        and _calendar_cache.get("data")
        and (now - float(_calendar_cache.get("ts") or 0)) < _CALENDAR_CACHE_SECS
    ):
        return list(_calendar_cache["data"])

    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
        ),
        "Accept": "application/json",
        "Cache-Control": "no-cache",
    }
    last_err: Exception | None = None
    for url in FF_WEEK_URLS:
        for attempt in range(max(1, retries)):
            try:
                r = requests.get(url, headers=headers, timeout=timeout)
                if r.status_code == 429:
                    wait = min(20.0, 1.5 * (2 ** attempt))
                    print(f"[NewsSignal] calendar 429 ({url}) — retry in {wait:.1f}s")
                    time.sleep(wait)
                    last_err = RuntimeError("calendar rate limited (429)")
                    continue
                r.raise_for_status()
                data = r.json()
                if not isinstance(data, list) or not data:
                    raise ValueError("Unexpected calendar payload")
                _calendar_cache["ts"] = time.time()
                _calendar_cache["data"] = data
                return data
            except Exception as ex:
                last_err = ex
                time.sleep(min(8.0, 1.0 * (2 ** attempt)))
        print(f"[NewsSignal] calendar source failed, trying next: {last_err}")
    
    if _calendar_cache.get("data"):
        print("[NewsSignal] using stale calendar cache")
        return list(_calendar_cache["data"])
    raise RuntimeError(f"Calendar fetch failed: {last_err}")


def event_tier(title: str, impact: str = "") -> str:
   
    t = (title or "").lower()
    if any(k in t for k in _SPEECH_KEYWORDS):
        return "S"
    if any(k in t for k in _TIER_A_KEYWORDS):
        return "A"
    if any(k in t for k in _TIER_B_KEYWORDS):
        return "B"
    if str(impact or "").upper() == "HIGH":
        return "B"
    return "C"


def _fetch_rss_headlines(limit_per_feed: int = 25) -> list[str]:
   
    now = time.time()
    if _rss_cache.get("items") and (now - float(_rss_cache.get("ts") or 0)) < _RSS_CACHE_SECS:
        return list(_rss_cache["items"])

    titles: list[str] = []
    headers = {"User-Agent": "Mozilla/5.0 (compatible; FLUXION-News/1.0)"}
    for url in _RSS_FEEDS:
        try:
            r = requests.get(url, headers=headers, timeout=12)
            if not r.ok:
                continue
            text = r.text or ""
            
            for m in re.finditer(r"<title>(?:<!\[CDATA\[)?(.*?)(?:\]\]>)?</title>", text, re.I | re.S):
                title = re.sub(r"\s+", " ", m.group(1)).strip()
                if not title or title.lower() in ("forex news", "fxstreet", "rss"):
                    continue
                titles.append(title)
                if len(titles) >= limit_per_feed * len(_RSS_FEEDS):
                    break
        except Exception as ex:
            print(f"[NewsSignal] RSS skip {url}: {ex}")
    _rss_cache["ts"] = time.time()
    _rss_cache["items"] = titles
    return titles


def _headline_currency_hits(title: str, currency: str) -> bool:
    t = title.lower()
    ccy = (currency or "").upper()
    aliases = {
        "USD": ("usd", "dollar", "fed", "fomc", "powell", "u.s.", "us "),
        "EUR": ("eur", "euro", "ecb", "lagarde", "eurozone", "euro zone"),
        "GBP": ("gbp", "pound", "sterling", "boe", "uk "),
        "JPY": ("jpy", "yen", "boj", "japan"),
        "AUD": ("aud", "aussie", "rba", "australia"),
        "CAD": ("cad", "loonie", "boc", "canada"),
        "NZD": ("nzd", "kiwi", "rbnz", "new zealand"),
        "CHF": ("chf", "franc", "snb", "swiss"),
        "XAU": ("gold", "xau"),
    }
    keys = aliases.get(ccy, (ccy.lower(),))
    return any(k in t for k in keys)


def rss_sentiment_for_currency(currency: str, headlines: list[str] | None = None) -> tuple[str | None, int, str]:
   
    headlines = headlines if headlines is not None else _fetch_rss_headlines()
    score = 0
    samples: list[str] = []
    for h in headlines:
        if not _headline_currency_hits(h, currency):
            continue
        hl = h.lower()
        bull = sum(1 for k in _BULLISH_HEADLINE if k in hl)
        bear = sum(1 for k in _BEARISH_HEADLINE if k in hl)
        if bull == bear:
            continue
        if bull > bear:
            score += 1
            samples.append(h[:90])
        else:
            score -= 1
            samples.append(h[:90])
    if score >= 2:
        return "BULLISH", abs(score), (samples[0] if samples else "")
    if score <= -2:
        return "BEARISH", abs(score), (samples[0] if samples else "")
    return None, abs(score), (samples[0] if samples else "")


def _parse_impact(raw: str) -> str:
    s = (raw or "").strip().lower()
    if s in ("high", "red"):
        return "HIGH"
    if s in ("medium", "med", "orange"):
        return "MEDIUM"
    return "LOW"


def _parse_num(raw: Any) -> float | None:
    if raw is None:
        return None
    s = str(raw).strip()
    if not s or s.upper() in ("N/A", "NA", "-", "—", ""):
        return None
    mult = 1.0
    su = s.upper().replace(",", "")
    if su.endswith("%"):
        su = su[:-1]
    if su.endswith("K"):
        mult = 1_000.0
        su = su[:-1]
    elif su.endswith("M"):
        mult = 1_000_000.0
        su = su[:-1]
    elif su.endswith("B"):
        mult = 1_000_000_000.0
        su = su[:-1]
    su = re.sub(r"[^\d.\-+]", "", su)
    try:
        return float(su) * mult
    except ValueError:
        return None


def _title_inverts_higher(title: str) -> bool:
    title_l = (title or "").lower()
    
    if "trade balance" in title_l or "current account" in title_l:
        return False
    return any(k in title_l for k in _NEGATIVE_IF_HIGHER)


def _bias_from_compare(
    title: str,
    left: float,
    right: float,
    *,
    mode: str,
) -> tuple[str | None, int]:
   
    if left == right:
        return None, 0
    base = max(abs(right), abs(left), 1e-9)
    gap = abs(left - right) / base
    if gap < _MIN_REL_GAP:
        return None, 0
    invert = _title_inverts_higher(title)
    stronger = left > right
    if invert:
        stronger = not stronger
    bias = "BULLISH" if stronger else "BEARISH"
    if mode == "actual_vs_forecast":
        
        conf = 82 + min(13, int(gap * 80))
    else:
        
        conf = 68 + min(18, int(gap * 90))
    return bias, int(conf)


def _heuristic_bias(
    title: str,
    forecast: Any,
    previous: Any,
    actual: Any = None,
) -> tuple[str | None, int, str | None]:
    
    a = _parse_num(actual)
    f = _parse_num(forecast)
    p = _parse_num(previous)
    if a is not None and f is not None:
        bias, conf = _bias_from_compare(title, a, f, mode="actual_vs_forecast")
        if bias:
            return bias, conf, "actual_vs_forecast"
    if f is not None and p is not None:
        bias, conf = _bias_from_compare(title, f, p, mode="forecast_vs_previous")
        if bias:
            return bias, conf, "forecast_vs_previous"
    return None, 0, None


def _merge_bias(
    heur_bias: str | None,
    heur_conf: int,
    ai: dict | None,
    *,
    title: str = "",
    currency: str = "",
    tier: str = "C",
    bias_mode: str | None = None,
    rss_bias: str | None = None,
) -> tuple[str | None, int, str]:
   
    ai = ai or {}
    ai_bias = str(ai.get("bias") or "").upper()
    if ai_bias not in ("BULLISH", "BEARISH", "NEUTRAL"):
        ai_bias = ""
    ai_conf = int(ai.get("confidence") or 0)
    rationale = str(ai.get("rationale") or "").strip()
    has_actual = bias_mode == "actual_vs_forecast"
    rss_bias = (rss_bias or "").upper() or None
    title_l = (title or "").lower()

   
    if not has_actual and tier in ("C", "S"):
        print(
            f"[NewsSignal] skip weak/pre-news: {currency} tier={tier} "
            f"{title[:40]!r}"
        )
        return None, 0, ""

    
    if not has_actual and any(k in title_l for k in _PRENEWS_SKIP_KEYWORDS):
        print(
            f"[NewsSignal] skip noisy pre-news event: {currency} {title[:40]!r}"
        )
        return None, 0, "Skipped - noisy regional event (wait for actual)"

    if heur_bias in ("BULLISH", "BEARISH"):
        
        if (
            not has_actual
            and rss_bias in ("BULLISH", "BEARISH")
            and rss_bias != heur_bias
            and tier != "A"
        ):
            print(
                f"[NewsSignal] RSS conflict skip: {currency} {title[:36]!r} "
                f"heur={heur_bias} rss={rss_bias}"
            )
            return None, 0, "Skipped - headlines conflict with calendar bias"

        if ai_bias in ("BULLISH", "BEARISH") and ai_bias != heur_bias:
            print(
                f"[NewsSignal] AI flip blocked: {currency} {title[:40]!r} "
                f"heur={heur_bias} ai={ai_bias} -> keep {heur_bias}"
            )
            conf = max(heur_conf, 70)
            if rss_bias == heur_bias:
                conf = min(95, conf + 5)
            return heur_bias, conf, rationale or "Rule engine (AI disagreed - ignored)"

        conf = heur_conf or 72
        if ai_bias == heur_bias:
            conf = max(conf, ai_conf, 75)
        if rss_bias == heur_bias:
            conf = min(95, conf + 6)
            if not rationale:
                rationale = "Confirmed by recent FX headlines"
        
        if tier == "A":
            conf = min(95, conf + 3)
        elif not has_actual and tier == "B":
            conf = min(conf, 82)
        return heur_bias, conf, rationale

    
    if ai_bias in ("BULLISH", "BEARISH") and tier == "A" and ai_conf >= 85:
        if rss_bias and rss_bias != ai_bias:
            return None, 0, "Skipped - AI vs headlines conflict"
        return ai_bias, ai_conf, rationale
    return None, 0, ""


def _to_local(dt_utc: datetime, tz_hours: float = 6.0) -> datetime:
    return dt_utc.astimezone(timezone(timedelta(hours=tz_hours)))


def _parse_ff_date(raw: str) -> datetime | None:
    
    s = (raw or "").strip()
    if not s:
        return None
    try:
        # 2026-07-26T19:50:00-04:00
        return datetime.fromisoformat(s)
    except ValueError:
        pass
    try:
        return datetime.strptime(s[:19], "%Y-%m-%dT%H:%M:%S").replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def filter_calendar_events(
    events: list[dict],
    *,
    pairs: list[str],
    n_days: int = 1,
    newsfilter: str = "all",
    tz_hours: float = 6.0,
) -> list[dict]:
    days = max(1, min(3, int(n_days or 1)))
    filt = str(newsfilter or "all").strip().lower()
    allowed_impacts = {"HIGH", "MEDIUM", "LOW"} if filt == "all" else {_parse_impact(filt)}
    wanted_ccy = currencies_from_pairs(pairs)
    now_local = datetime.now(timezone(timedelta(hours=tz_hours)))
    end_local = now_local + timedelta(days=days)

    out: list[dict] = []
    for ev in events or []:
        country = str(ev.get("country") or "").upper()
        ccy = _FF_COUNTRY_TO_CCY.get(country, country)
        if wanted_ccy and ccy not in wanted_ccy:
            continue
        impact = _parse_impact(ev.get("impact") or "")
        if impact not in allowed_impacts:
            continue
        dt = _parse_ff_date(str(ev.get("date") or ""))
        if not dt:
            continue
        local = _to_local(dt, tz_hours)
        if local < now_local - timedelta(minutes=5):
            continue
        if local > end_local:
            continue
        title = str(ev.get("title") or "").strip()
        if not title:
            continue
        bias, conf, mode = _heuristic_bias(
            title, ev.get("forecast"), ev.get("previous"), ev.get("actual"),
        )
        tier = event_tier(title, impact)
        out.append({
            "title": title,
            "currency": ccy,
            "impact": impact,
            "forecast": ev.get("forecast") if ev.get("forecast") not in (None, "") else "N/A",
            "previous": ev.get("previous") if ev.get("previous") not in (None, "") else "N/A",
            "actual": ev.get("actual") if ev.get("actual") not in (None, "") else "N/A",
            "dt_local": local,
            "date_fmt": local.strftime("%d-%m-%Y"),
            "time_fmt": local.strftime("%H:%M"),
            "bias": bias,
            "confidence": conf,
            "bias_mode": mode,
            "tier": tier,
            "source": "ForexFactory",
        })
    out.sort(key=lambda x: x["dt_local"])
    return out


def _pairs_for_bias(pairs: list[str], currency: str, bias: str) -> tuple[list[str], list[str]]:
    
    call: list[str] = []
    put: list[str] = []
    ccy = (currency or "").upper()
    bullish = (bias or "").upper() == "BULLISH"
    for raw in pairs:
        sp = slash_pair(raw)
        if "/" not in sp:
            continue
        base, quote = sp.split("/", 1)
        if ccy not in (base, quote):
            continue
        if bullish:
            if base == ccy:
                call.append(sp)
            else:
                put.append(sp)
        else:
            if base == ccy:
                put.append(sp)
            else:
                call.append(sp)
    return call, put


def analyze_events_with_gemini(
    events: list[dict],
    pairs: list[str],
    gemini_keys: list[str],
    *,
    model: str = "gemini-2.0-flash",
) -> dict[int, dict]:
    
    global _gemini_idx
    if not events or not gemini_keys:
        return {}

    compact = []
    for i, ev in enumerate(events[:40]):
        compact.append({
            "id": i,
            "event": ev["title"],
            "currency": ev["currency"],
            "impact": ev["impact"],
            "forecast": ev["forecast"],
            "previous": ev["previous"],
            "actual": ev.get("actual", "N/A"),
            "time": f"{ev['date_fmt']} {ev['time_fmt']}",
            "heuristic_bias": ev.get("bias"),
            "bias_mode": ev.get("bias_mode"),
            "tier": ev.get("tier", "C"),
        })

    rss_snip = []
    try:
        for h in _fetch_rss_headlines()[:12]:
            rss_snip.append(h[:100])
    except Exception:
        pass

    prompt = (
        "You are a senior forex binary-options news analyst for FLUXION PRO.\n"
        "Task: for each event, decide if the EVENT CURRENCY is BULLISH or BEARISH "
        "for the immediate candle after the release.\n\n"
        "CRITICAL RULES:\n"
        "1) Prefer ACTUAL vs FORECAST when actual is a real number "
        "(this is the surprise that moves the candle).\n"
        "2) If actual is missing, use FORECAST vs PREVIOUS as expected bias.\n"
        "3) For unemployment / jobless / claims / inventories: HIGHER = BEARISH.\n"
        "4) For CPI / GDP / retail sales / employment / trade balance surplus: "
        "HIGHER = BULLISH for that currency.\n"
        "5) bias is about the EVENT CURRENCY only "
        "(EUR bullish != always sell EURUSD — pair side is handled elsewhere).\n"
        "6) If heuristic_bias is present, CONFIRM it unless the numbers clearly "
        "contradict it. Do NOT flip casually.\n"
        "7) Speeches / empty numbers / tier C → NEUTRAL.\n"
        "8) Use recent headlines only as soft context, not to invent a side.\n\n"
        f"Selected pairs (context only): {', '.join(pairs[:40])}\n"
        f"Recent FX headlines:\n{json.dumps(rss_snip, ensure_ascii=False)}\n\n"
        f"Events JSON:\n{json.dumps(compact, ensure_ascii=False)}\n\n"
        "Respond ONLY with JSON (no markdown):\n"
        '{"results":[{"id":0,"bias":"BULLISH","confidence":85,'
        '"rationale":"1 short sentence"}]}\n'
        "bias must be BULLISH, BEARISH, or NEUTRAL. confidence 60-95 integer."
    )

    keys = [k for k in gemini_keys if k]
    if not keys:
        return {}

    last_err = ""
    for _ in range(len(keys)):
        with _gemini_lock:
            key = keys[_gemini_idx % len(keys)]
        url = (
            f"https://generativelanguage.googleapis.com/v1beta/models/"
            f"{model}:generateContent?key={key}"
        )
        try:
            resp = requests.post(
                url,
                headers={"Content-Type": "application/json"},
                json={
                    "contents": [{"parts": [{"text": prompt}]}],
                    "generationConfig": {
                        "temperature": 0.05,
                        "maxOutputTokens": 2048,
                        "responseMimeType": "application/json",
                    },
                },
                timeout=45,
            )
            raw = resp.json()
            if "error" in raw:
                msg = str(raw["error"].get("message", ""))
                last_err = msg
                if any(k in msg.lower() for k in ("quota", "rate", "resource", "429")):
                    with _gemini_lock:
                        _gemini_idx += 1
                    continue
                break
            cands = raw.get("candidates") or []
            if not cands:
                last_err = "no candidates"
                with _gemini_lock:
                    _gemini_idx += 1
                continue
            text = (cands[0].get("content") or {}).get("parts") or [{}]
            text_raw = str(text[0].get("text") or "")
            start = text_raw.find("{")
            end = text_raw.rfind("}") + 1
            if start < 0 or end <= 0:
                last_err = "no json"
                break
            data = json.loads(text_raw[start:end])
            out: dict[int, dict] = {}
            for row in data.get("results") or []:
                try:
                    idx = int(row.get("id"))
                except Exception:
                    continue
                bias = str(row.get("bias") or "NEUTRAL").upper()
                if bias not in ("BULLISH", "BEARISH", "NEUTRAL"):
                    bias = "NEUTRAL"
                conf = max(60, min(95, int(row.get("confidence") or 75)))
                out[idx] = {
                    "bias": bias,
                    "confidence": conf,
                    "rationale": str(row.get("rationale") or "").strip(),
                }
            return out
        except Exception as ex:
            last_err = str(ex)
            with _gemini_lock:
                _gemini_idx += 1
            continue
    if last_err:
        print(f"[NewsAI] Gemini failed: {last_err[:160]}")
    return {}


def _pair_direction_label(call_pairs: list[str], put_pairs: list[str]) -> str:
   
    prefer = ("EUR/USD", "GBP/USD", "USD/JPY", "XAU/USD", "AUD/USD", "USD/CAD")
    for p in prefer:
        if p in call_pairs:
            return f"{p} → CALL / BUY ⬆️"
        if p in put_pairs:
            return f"{p} → PUT / SELL ⬇️"
    if call_pairs:
        return f"{call_pairs[0]} → CALL / BUY ⬆️"
    if put_pairs:
        return f"{put_pairs[0]} → PUT / SELL ⬇️"
    return "NEUTRAL"


def build_news_events(
    *,
    pairs: list[str],
    n_days: int = 1,
    newsfilter: str = "all",
    tz_hours: float = 6.0,
    use_ai: bool = True,
    gemini_keys: list[str] | None = None,
) -> dict[str, Any]:
    
    clean_pairs = []
    seen = set()
    for p in pairs or []:
        sp = slash_pair(p)
        if sp and sp not in seen:
            seen.add(sp)
            clean_pairs.append(sp)
    if not clean_pairs:
        return {"status": "error", "message": "No pairs selected."}

    try:
        calendar = fetch_ff_calendar()
    except Exception as ex:
        return {"status": "error", "message": f"Calendar fetch failed: {ex}"}

    filtered = filter_calendar_events(
        calendar,
        pairs=clean_pairs,
        n_days=n_days,
        newsfilter=newsfilter,
        tz_hours=tz_hours,
    )
    if not filtered:
        return {
            "status": "success",
            "events": [],
            "total": 0,
            "ai_used": False,
            "message": "No matching news events for your filters.",
        }

    ai_map: dict[int, dict] = {}
    ai_used = False
    if use_ai and gemini_keys:
        ai_map = analyze_events_with_gemini(filtered, clean_pairs, gemini_keys)
        ai_used = bool(ai_map)

    
    try:
        headlines = _fetch_rss_headlines()
    except Exception:
        headlines = []
    rss_by_ccy: dict[str, str | None] = {}
    for ccy in {str(ev.get("currency") or "") for ev in filtered}:
        if not ccy:
            continue
        rb, _, _ = rss_sentiment_for_currency(ccy, headlines)
        rss_by_ccy[ccy] = rb

    cards = []
    skipped = 0
    for i, ev in enumerate(filtered):
        heur_bias = ev.get("bias")
        heur_conf = int(ev.get("confidence") or 0)
        ccy = str(ev.get("currency") or "")
        bias, conf, rationale = _merge_bias(
            heur_bias,
            heur_conf,
            ai_map.get(i),
            title=str(ev.get("title") or ""),
            currency=ccy,
            tier=str(ev.get("tier") or "C"),
            bias_mode=ev.get("bias_mode"),
            rss_bias=rss_by_ccy.get(ccy),
        )
        if not bias:
            skipped += 1
            continue
        call_pairs, put_pairs = _pairs_for_bias(clean_pairs, ev["currency"], bias)
        if not call_pairs and not put_pairs:
            continue
        direction = _pair_direction_label(call_pairs, put_pairs)
        
        eurusd_side = (
            "CALL" if "EUR/USD" in call_pairs else
            ("PUT" if "EUR/USD" in put_pairs else "-")
        )
        print(
            f"[NewsSignal] {ev.get('time_fmt')} {ev['currency']} "
            f"{(ev.get('title') or '')[:36]!r} bias={bias} tier={ev.get('tier')} "
            f"mode={ev.get('bias_mode') or '-'} rss={rss_by_ccy.get(ccy) or '-'} "
            f"EURUSD={eurusd_side} "
            f"F={ev.get('forecast')} P={ev.get('previous')} A={ev.get('actual')}"
        )
        entry_dt = ev["dt_local"] - timedelta(seconds=2)
        cards.append({
            "date": ev["date_fmt"],
            "time": ev["time_fmt"],
            "event": ev["title"],
            "impact": ev["impact"],
            "forecast": ev["forecast"],
            "previous": ev["previous"],
            "actual": ev.get("actual", "N/A"),
            "currency": ev["currency"],
            "direction": direction,
            "bias": bias,
            "confidence": conf or 75,
            "rationale": rationale,
            "call_pairs": call_pairs,
            "put_pairs": put_pairs,
            "entry": entry_dt.strftime("%H:%M:%S"),
            "bias_mode": ev.get("bias_mode"),
            "tier": ev.get("tier"),
        })

    return {
        "status": "success",
        "events": cards,
        "total": len(cards),
        "ai_used": ai_used,
        "skipped": skipped,
        "tz_label": f"UTC{'+' if tz_hours >= 0 else ''}{int(tz_hours) if tz_hours == int(tz_hours) else tz_hours}",
        "calendar_count": len(filtered),
    }


def _wrap_pairs(pairs: list[str], per_line: int = 3) -> str:
    if not pairs:
        return "—"
    lines = []
    for i in range(0, len(pairs), per_line):
        chunk = pairs[i:i + per_line]
        lines.append("  ".join(chunk))
    return "\n     ".join(lines) if len(lines) > 1 else lines[0]


def _ticket_side(event: dict) -> tuple[str, str]:
    dir_lbl = str(event.get("direction") or "")
    if "→" in dir_lbl:
        pair, rest = dir_lbl.split("→", 1)
        side = "PUT" if ("PUT" in rest.upper() or "SELL" in rest.upper()) else "CALL"
        return pair.strip(), side
    call = list(event.get("call_pairs") or [])
    put = list(event.get("put_pairs") or [])
    if call:
        return call[0], "CALL"
    if put:
        return put[0], "PUT"
    return "—", "—"


def build_news_signal_parts(
    event: dict,
    *,
    events_today: int,
    tz_label: str = "UTC+6",
    owner: str = "@Rohailtrader",
    bot_username: str = "RohailBot",
    ai_used: bool = False,
) -> list[tuple[str, str | None]]:
    impact = str(event.get("impact") or "LOW").upper()
    date_fmt = str(event.get("date") or "—").replace("-", ".")
    time_s = str(event.get("time") or "—")
    entry = str(event.get("entry") or time_s)
    currency = str(event.get("currency") or "USD")
    flag = _CURRENCY_FLAGS.get(currency, "🏳️")
    event_name = str(event.get("event") or "—")
    forecast = event.get("forecast") or "N/A"
    previous = event.get("previous") or "N/A"
    actual = event.get("actual") or "—"
    if actual in ("N/A", "", None):
        actual = "—"
    call_line = _wrap_pairs(list(event.get("call_pairs") or []))
    put_line = _wrap_pairs(list(event.get("put_pairs") or []))
    owner_disp = owner if str(owner).startswith("@") else f"@{owner}"
    conf = event.get("confidence") or ""
    side_pair, side = _ticket_side(event)
    conf_bit = f" | {conf}%" if conf else ""

    parts: list[tuple[str, str | None]] = [
        ("▰▱ NEWS TICKET ▱▰\n", None),
        ("🔥", "fire"), (f" {impact}  ·  {currency}{flag}  ·  {tz_label}\n\n", None),
        ("📅", "calendar"), (f" {date_fmt}\n", None),
        ("⏰", "alarm"), (f" {time_s}\n", None),
        ("📰", "news"), (f" {event_name}\n\n", None),
        ("😮", "surprise"), (" SIDE\n", None),
        (f"{side_pair}  {side}\n\n", None),
        ("⬆️", "up_arr"), (f" CALL  {call_line}\n", None),
        ("⬇️", "down_arr"), (f" PUT   {put_line}\n\n", None),
        ("📈", "trend_up"), (f" F {forecast}  |  ", None),
        ("📉", "trend_down"), (f" P {previous}  |  A {actual}{conf_bit}\n\n", None),
        ("⏱", "timer"), (f" ENTRY  {entry}\n", None),
        ("🔄", "refresh"), (" MTG 1 if loss\n", None),
        ("✏️", "writing"), (f" {owner_disp}", None),
    ]
    return parts


def parts_to_text_and_entities(
    parts: list[tuple[str, str | None]],
    *,
    use_prem: bool,
    extra_emoji_ids: dict | None = None,
) -> tuple[str, list[dict]]:
    ids = dict(NEWS_EMOJI_IDS)
    if extra_emoji_ids:
        ids.update(extra_emoji_ids)
    text = "".join(s for s, _ in parts)
    entities: list[dict] = [{"type": "bold", "offset": 0, "length": _u16len(text)}]
    if use_prem:
        offset = 0
        for s, key in parts:
            if key is not None:
                doc_id = ids.get(key, 0)
                if doc_id:
                    entities.append({
                        "type": "custom_emoji",
                        "offset": offset,
                        "length": _u16len(s),
                        "custom_emoji_id": str(doc_id),
                    })
            offset += _u16len(s)
    entities.sort(key=lambda x: (x["offset"], x["type"] != "bold"))
    return text, entities
