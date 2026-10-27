module

public import Certificates.Data.Kernel.L34W.Model
public import Certificates.Data.GrSLitL34FactsRealBCheck
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def dec (x : ℕ) : MElt := (x / 16, ((x / 4 % 4 : ℕ) : ZMod 4), ((x % 4 : ℕ) : ZMod 4))

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem mk_eq (m a b : ℕ) : mk m a b = 16 * m + 4 * (a % 4) + b % 4 := rfl

theorem mk_lt {m a b : ℕ} (hm : m < 64) : mk m a b < 1024 := by
  rw [mk_eq]
  have := Nat.mod_lt a (show 4 > 0 by norm_num)
  have := Nat.mod_lt b (show 4 > 0 by norm_num)
  omega

theorem dec_mk (m a b : ℕ) : dec (mk m a b) = (m, (a : ZMod 4), (b : ZMod 4)) := by
  rw [mk_eq]
  have ha := Nat.mod_lt a (show 4 > 0 by norm_num)
  have hb := Nat.mod_lt b (show 4 > 0 by norm_num)
  have e1 : (16 * m + 4 * (a % 4) + b % 4) / 16 = m := by omega
  have e2 : (16 * m + 4 * (a % 4) + b % 4) / 4 % 4 = a % 4 := by omega
  have e3 : (16 * m + 4 * (a % 4) + b % 4) % 4 = b % 4 := by omega
  rw [dec, e1, e2, e3, ZMod.natCast_mod, ZMod.natCast_mod]

theorem dec_lt {x : ℕ} (hx : x < 1024) : (dec x).1 < 64 := by
  change x / 16 < 64
  omega

theorem dec_sixteen (t : ℕ) : dec (16 * t) = (t, 0, 0) := by
  have e1 : 16 * t / 16 = t := by omega
  have e2 : 16 * t / 4 % 4 = 0 := by omega
  have e3 : 16 * t % 4 = 0 := by omega
  rw [dec, e1, e2, e3, Nat.cast_zero]

theorem hex3_eq (b : ByteArray) (o : ℕ) : hex3 b o = CFSG.Monster.B.Max2.Native.hexAt b o 3 := by
  simp only [hex3, CFSG.Monster.B.Max2.Native.hexAt, hexDigit, CFSG.Monster.B.Max2.Native.hexVal,
    Nat.add_zero]
  ring

theorem ofFn_get! {n i : ℕ} (f : Fin n → ℕ) (hi : i < n) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

theorem hex3_of_hex {s : String} {cs : List Char} {n N : ℕ} {F : ℕ → ℕ} (hs : s = String.ofList cs)
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs 3 n 12 N F = true) {j i : ℕ} (hj : j < N) (hi : i < n) :
    hex3 s.toUTF8 (3 * (n * j + i)) = ent F j i := by
  have e := congrArg (fun a : Array ℕ => a[i]!) (CFSG.KC.Misc.HexFlat.hexTable3_sound h j hj)
  simp only [CFSG.Monster.B.Fischer.hexTable3, unpack] at e
  rw [ofFn_get! _ hi, ofFn_get! _ hi, ← hs] at e
  rw [hex3_eq, e]
  rfl

@[expose] def T1Of (T : ℕ → ℕ) : Prop := ∀ k l, k < 64 → l < 64 → t1Entry k l = quad (ent T k l)

@[expose] def AlOf (A : ℕ → ℕ) : Prop := ∀ i k, i < 36 → k < 66 → alphaEntry i k = quad (ent A i k)

theorem t1Entry_of_hex {cs : List Char} {F : ℕ → ℕ} (hs : realT1Hex = String.ofList cs)
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs 3 64 12 64 F = true) : T1Of F := by
  intro k l hk hl
  rw [t1Entry, realT1]
  try simp only
  rw [ofFn_get! _ (show 64 * k + l < 4096 by omega)]
  exact congrArg quad (hex3_of_hex hs h hk hl)

theorem alphaEntry_of_hex {cs : List Char} {F : ℕ → ℕ} (hs : realAlphaHex = String.ofList cs)
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs 3 66 12 36 F = true) : AlOf F := by
  intro i k hi hk
  rw [alphaEntry, realAlpha]
  try simp only
  rw [ofFn_get! _ (show 66 * i + k < 2376 by omega)]
  exact congrArg quad (hex3_of_hex hs h hi hk)

variable {T A : ℕ → ℕ}

theorem mulC_eq (x y : ℕ) : mulC T x y = mk (ent T (x / 16) (y / 16) / 48)
    (x / 4 % 4 + y / 4 % 4 + ent T (x / 16) (y / 16) % 48 / 12)
    (x % 4 + y % 4 + ent T (x / 16) (y / 16) % 12 / 3) := by
  unfold mulC
  rw [strictN_eq']
  rfl

theorem dec_mulC (hT : T1Of T) {x y : ℕ} (hx : x < 1024) (hy : y < 1024) :
    dec (mulC T x y) = mulM (dec x) (dec y) := by
  rw [mulC_eq, dec_mk]
  simp only [dec, mulM]
  rw [hT _ _ (by omega) (by omega)]
  simp only [quad]
  push_cast
  rfl

theorem betaRepC_eq (i x : ℕ) : betaRepC A i x = mk (ent A i (x / 16) / 48)
    (ent A i (x / 16) % 48 / 12 + (x / 4 % 4 * (ent A i 64 % 48 / 12) +
      x % 4 * (ent A i 65 % 48 / 12)))
    (ent A i (x / 16) % 12 / 3 + (x / 4 % 4 * (ent A i 64 % 12 / 3) +
      x % 4 * (ent A i 65 % 12 / 3))) := by
  unfold betaRepC
  simp only [strictN_eq']
  rfl

theorem dec_betaRepC (hA : AlOf A) {i x : ℕ} (hi : i < 36) (hx : x < 1024) :
    dec (betaRepC A i x) = betaRepM i (dec x) := by
  rw [betaRepC_eq, dec_mk]
  simp only [dec, betaRepM]
  rw [hA i _ hi (by omega), hA i 64 hi (by norm_num), hA i 65 hi (by norm_num)]
  simp only [quad]
  push_cast
  rfl

theorem firstC_succ (p : ℕ → Bool) (n : ℕ) : firstC p (n + 1) =
    if firstC p n < n then firstC p n else if p n = true then n else n + 1 := by
  change strictN (firstC p n) (fun r => nIf(Nat.blt r n, r, nIf(p n, n, Nat.succ n))) = _
  rw [strictN_eq']
  by_cases h1 : firstC p n < n
  · rw [if_pos h1, Nat.blt_eq.mpr h1]
  · have h2 : Nat.blt (firstC p n) n = false := by
      cases h : Nat.blt (firstC p n) n
      · rfl
      · exact absurd (Nat.blt_eq.mp h) h1
    rw [if_neg h1, h2]
    cases p n <;> rfl

theorem firstC_spec (p : ℕ → Bool) : ∀ n, firstC p n ≤ n ∧
    (List.range n).find? p = if firstC p n < n then some (firstC p n) else none
  | 0 => ⟨Nat.le_refl 0, rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := firstC_spec p n
    rw [firstC_succ, List.range_succ, List.find?_append, h2]
    by_cases h : firstC p n < n
    · rw [if_pos h, if_pos h, if_pos (by omega)]
      exact ⟨by omega, rfl⟩
    · have e : firstC p n = n := by omega
      rw [if_neg h, if_neg h]
      cases hp : p n
      · simp [hp]
      · simp [hp]

theorem find?_congr' {p q : ℕ → Bool} : ∀ {l : List ℕ}, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      find?_congr' (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem invIdxC_eq (hT : T1Of T) {k : ℕ} (hk : k < 64) : invIdxC T k = invIdx k := by
  have e : (List.range 64).find? (fun k' => (t1Entry k k').1 == 0) =
      (List.range 64).find? (fun k' => Nat.beq (ent T k k' / 48) 0) := by
    refine find?_congr' fun a ha => ?_
    rw [hT k a hk (List.mem_range.1 ha), quad]
    cases h : Nat.beq (ent T k a / 48) 0
    · rw [beq_eq_false_iff_ne]
      exact Nat.ne_of_beq_eq_false h
    · rw [beq_iff_eq]
      exact Nat.eq_of_beq_eq_true h
  unfold invIdxC invIdx
  rw [strictN_eq', e, (firstC_spec _ 64).2]
  change nIf(Nat.blt (firstC (fun k' => Nat.beq (ent T k k' / 48) 0) 64) 64, _, _) = _
  by_cases h : firstC (fun k' => Nat.beq (ent T k k' / 48) 0) 64 < 64
  · rw [if_pos h, Nat.blt_eq.mpr h]
    rfl
  · have h2 : Nat.blt (firstC (fun k' => Nat.beq (ent T k k' / 48) 0) 64) 64 = false := by
      cases h' : Nat.blt (firstC (fun k' => Nat.beq (ent T k k' / 48) 0) 64) 64
      · rfl
      · exact absurd (Nat.blt_eq.mp h') h
    rw [if_neg h, h2]
    rfl

theorem invIdxC_lt (k : ℕ) : invIdxC T k < 64 := by
  unfold invIdxC
  rw [strictN_eq']
  generalize firstC (fun k' => Nat.beq (Nat.div (ent T k k') 48) 0) 64 = r
  cases h : Nat.blt r 64
  · change 0 < 64
    norm_num
  · exact Nat.blt_eq.mp h

theorem invC_eq (x : ℕ) : invC T x = mk (invIdxC T (x / 16))
    (8 - ent T (x / 16) (invIdxC T (x / 16)) % 48 / 12 - x / 4 % 4)
    (8 - ent T (x / 16) (invIdxC T (x / 16)) % 12 / 3 - x % 4) := by
  unfold invC
  simp only [strictN_eq']
  rfl

theorem cast_eight_sub {c a : ℕ} (hc : c < 4) (ha : a < 4) :
    ((8 - c - a : ℕ) : ZMod 4) = -(c : ZMod 4) - (a : ZMod 4) := by
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have e : ((8 : ℕ) : ZMod 4) = 0 := by decide
  rw [e]
  ring

theorem dec_invC (hT : T1Of T) {x : ℕ} (hx : x < 1024) : dec (invC T x) = invM (dec x) := by
  have hk : x / 16 < 64 := by omega
  rw [invC_eq, dec_mk]
  simp only [dec, invM]
  rw [invIdxC_eq hT hk, hT _ _ hk (invIdxC_eq hT hk ▸ invIdxC_lt _), quad]
  simp only
  rw [cast_eight_sub (by omega) (by omega), cast_eight_sub (by omega) (by omega)]

theorem bounds_T (hb : boundsOK T A = true) {k l : ℕ} (hk : k < 64) (hl : l < 64) :
    ent T k l < 3072 := by
  unfold boundsOK at hb
  rw [bAnd_iff] at hb
  exact Nat.blt_eq.mp (allN_spec (allN_spec hb.1 k hk) l hl)

theorem bounds_A (hb : boundsOK T A = true) {i k : ℕ} (hi : i < 36) (hk : k < 66) :
    ent A i k < 3072 := by
  unfold boundsOK at hb
  rw [bAnd_iff] at hb
  exact Nat.blt_eq.mp (allN_spec (allN_spec hb.2 i hi) k hk)

theorem mulC_lt (hb : boundsOK T A = true) {x y : ℕ} (hx : x < 1024) (hy : y < 1024) :
    mulC T x y < 1024 := by
  rw [mulC_eq]
  have := bounds_T hb (show x / 16 < 64 by omega) (show y / 16 < 64 by omega)
  exact mk_lt (by omega)

theorem betaRepC_lt (hb : boundsOK T A = true) {i x : ℕ} (hi : i < 36) (hx : x < 1024) :
    betaRepC A i x < 1024 := by
  rw [betaRepC_eq]
  have := bounds_A hb hi (show x / 16 < 66 by omega)
  exact mk_lt (by omega)

theorem invC_lt {x : ℕ} : invC T x < 1024 := by
  rw [invC_eq]
  exact mk_lt (invIdxC_lt _)

theorem betaC_eq (t i x : ℕ) :
    betaC T A t i x = mulC T (mulC T (16 * t) (betaRepC A i x)) (invC T (16 * t)) := rfl

theorem betaC_lt (hb : boundsOK T A = true) {t i x : ℕ} (ht : t < 64) (hi : i < 36)
    (hx : x < 1024) : betaC T A t i x < 1024 := by
  rw [betaC_eq]
  exact mulC_lt hb (mulC_lt hb (by omega) (betaRepC_lt hb hi hx)) invC_lt

theorem dec_betaC (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) {t i x : ℕ} (ht : t < 64)
    (hi : i < 36) (hx : x < 1024) : dec (betaC T A t i x) = betaYM t i (dec x) := by
  have h16 : 16 * t < 1024 := by omega
  rw [betaC_eq, dec_mulC hT (mulC_lt hb h16 (betaRepC_lt hb hi hx)) invC_lt,
    dec_mulC hT h16 (betaRepC_lt hb hi hx), dec_betaRepC hA hi hx, dec_invC hT h16, dec_sixteen]
  rfl

theorem mulM_ctr (k l : ℕ) (a b c d : ZMod 4) :
    mulM (k, a, b) (l, c, d) =
      ((mulM (k, 0, 0) (l, 0, 0)).1, (mulM (k, 0, 0) (l, 0, 0)).2.1 + (a + c),
        (mulM (k, 0, 0) (l, 0, 0)).2.2 + (b + d)) := by
  simp only [mulM]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem betaRepM_ctr (i k : ℕ) (a b : ZMod 4) :
    betaRepM i (k, a, b) =
      ((betaRepM i (k, 0, 0)).1,
        (betaRepM i (k, 0, 0)).2.1 +
          (a * ((alphaEntry i 64).2.1 : ZMod 4) + b * ((alphaEntry i 65).2.1 : ZMod 4)),
        (betaRepM i (k, 0, 0)).2.2 +
          (a * ((alphaEntry i 64).2.2.1 : ZMod 4) + b * ((alphaEntry i 65).2.2.1 : ZMod 4))) := by
  simp only [betaRepM]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem betaYM_ctr (t i k : ℕ) (a b : ZMod 4) :
    betaYM t i (k, a, b) =
      ((betaYM t i (k, 0, 0)).1,
        (betaYM t i (k, 0, 0)).2.1 +
          (a * ((alphaEntry i 64).2.1 : ZMod 4) + b * ((alphaEntry i 65).2.1 : ZMod 4)),
        (betaYM t i (k, 0, 0)).2.2 +
          (a * ((alphaEntry i 64).2.2.1 : ZMod 4) + b * ((alphaEntry i 65).2.2.1 : ZMod 4))) := by
  simp only [betaYM, mulM, betaRepM]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem mulM_sq_ctr (k : ℕ) (a b : ZMod 4) :
    mulM (k, a, b) (k, a, b) =
      ((mulM (k, 0, 0) (k, 0, 0)).1, (mulM (k, 0, 0) (k, 0, 0)).2.1 + 2 * a,
        (mulM (k, 0, 0) (k, 0, 0)).2.2 + 2 * b) := by
  simp only [mulM]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

end CFSG.KC.L34W

end
