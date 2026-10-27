module

public import Certificates.Data.Kernel.S1277KQ
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zz
public import CFSG.Certificates.Kernel.S1277KMLPrim
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.S1277Q

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.S1277Q CFSG.KS.S1277ML

theorem fld_eq (t w i : ℕ) : fld t w i = t / 2 ^ (w * i) % 2 ^ w := by
  change (t >>> (w * i)) &&& ((1 <<< w) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem lor_sh {x r w : ℕ} (hx : x < 2 ^ w) : Nat.lor x (Nat.shiftLeft r w) = x + 2 ^ w * r := by
  change x ||| r <<< w = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  ring

theorem fld_cons0 {x r w : ℕ} (hx : x < 2 ^ w) : fld (x + 2 ^ w * r) w 0 = x := by
  rw [fld_eq, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hx]

theorem fld_consS {x r w : ℕ} (hx : x < 2 ^ w) (k : ℕ) :
    fld (x + 2 ^ w * r) w (k + 1) = fld r w k := by
  rw [fld_eq, fld_eq, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * k)),
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hx,
    Nat.zero_add]

def recP (w : ℕ) (g : ℕ → ℕ → ℕ) (l : List ℕ) (i : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun p _ r i => Nat.lor (g p i) (Nat.shiftLeft (r (Nat.succ i)) w)) l i

theorem recP_lt {w : ℕ} {g : ℕ → ℕ → ℕ} (hg : ∀ p i, g p i < 2 ^ w) :
    ∀ l i, recP w g l i < 2 ^ (w * l.length)
  | [], _ => Nat.two_pow_pos _
  | p :: l, i => by
    change Nat.lor (g p i) (Nat.shiftLeft (recP w g l (i + 1)) w) < _
    rw [lor_sh (hg p i), List.length_cons, Nat.mul_succ, Nat.pow_add]
    have h1 := recP_lt hg l (i + 1)
    have h2 := hg p i
    have h3 : 2 ^ w * (recP w g l (i + 1) + 1) ≤ 2 ^ w * 2 ^ (w * l.length) :=
      Nat.mul_le_mul_left _ h1
    nlinarith

theorem recP_fld {w : ℕ} {g : ℕ → ℕ → ℕ} (hg : ∀ p i, g p i < 2 ^ w) :
    ∀ l i k, k < l.length → fld (recP w g l i) w k = g (l.getD k 0) (i + k)
  | [], _, _, hk => absurd hk (by simp)
  | p :: l, i, k, hk => by
    change fld (Nat.lor (g p i) (Nat.shiftLeft (recP w g l (i + 1)) w)) w k = _
    rw [lor_sh (hg p i)]
    cases k with
    | zero => rw [fld_cons0 (hg p i)]; rfl
    | succ k =>
      rw [fld_consS (hg p i), recP_fld hg l (i + 1) k (by simpa using hk), List.getD_cons_succ]
      congr 1
      omega

theorem packL_fld {w : ℕ} : ∀ l : List ℕ, (∀ x ∈ l, x < 2 ^ w) →
    ∀ k, k < l.length → fld (packL w l) w k = l.getD k 0
  | [], _, _, hk => absurd hk (by simp)
  | x :: l, hl, k, hk => by
    change fld (Nat.lor x (Nat.shiftLeft (packL w l) w)) w k = _
    have hx : x < 2 ^ w := hl x (by simp)
    rw [lor_sh hx]
    cases k with
    | zero => rw [fld_cons0 hx]; rfl
    | succ k =>
      rw [fld_consS hx, packL_fld l (fun y hy => hl y (by simp [hy])) k (by simpa using hk),
        List.getD_cons_succ]

def posMaskA (f : ℕ → Bool) (l : List ℕ) (i : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun x _ r i => Nat.lor (Bool.rec (motive := fun _ => ℕ) 0
      (Nat.shiftLeft 1 i) (f x)) (r (Nat.succ i))) l i

theorem testBit_posMaskA (f : ℕ → Bool) : ∀ (l : List ℕ) (i j : ℕ),
    (posMaskA f l i).testBit j = true ↔ ∃ k < l.length, j = i + k ∧ f (l.getD k 0) = true
  | [], i, j => by
    change (0 : ℕ).testBit j = true ↔ _
    simp
  | x :: l, i, j => by
    have e : (Bool.rec (motive := fun _ => ℕ) 0 (Nat.shiftLeft 1 i) (f x)).testBit j =
        (f x && decide (i = j)) := by
      cases f x
      · simp
      · change (1 <<< i).testBit j = _
        simp [Nat.one_shiftLeft, Nat.testBit_two_pow]
    change ((Bool.rec (motive := fun _ => ℕ) 0 (Nat.shiftLeft 1 i) (f x)) |||
      (posMaskA f l (i + 1))).testBit j = true ↔ _
    rw [Nat.testBit_or, e, Bool.or_eq_true, testBit_posMaskA f l (i + 1) j]
    constructor
    · rintro (h | ⟨k, hk, rfl, hf⟩)
      · rw [Bool.and_eq_true, decide_eq_true_iff] at h
        exact ⟨0, by simp, by omega, by simpa using h.1⟩
      · exact ⟨k + 1, by simpa using hk, by omega, by simpa using hf⟩
    · rintro ⟨k, hk, rfl, hf⟩
      cases k with
      | zero =>
        left
        simp only [List.getD_cons_zero] at hf
        simp [hf]
      | succ k =>
        right
        exact ⟨k, by simpa using hk, by omega, by simpa using hf⟩

theorem testBit_posMask (f : ℕ → Bool) (l : List ℕ) (j : ℕ) :
    (posMask f l).testBit j = true ↔ j < l.length ∧ f (l.getD j 0) = true := by
  change (posMaskA f l 0).testBit j = true ↔ _
  rw [testBit_posMaskA]
  constructor
  · rintro ⟨k, hk, rfl, hf⟩
    simpa using And.intro hk hf
  · rintro ⟨hj, hf⟩
    exact ⟨j, hj, by omega, hf⟩

theorem posMask_lt (f : ℕ → Bool) (l : List ℕ) (hl : l.length ≤ 136) : posMask f l < 2 ^ 136 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    cases h : (posMask f l).testBit i
    · rfl
    · have := ((testBit_posMask f l i).1 h).1
      omega

def posOfA (q : ℕ) (l : List ℕ) (i : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 255)
    (fun x _ r i => Bool.rec (motive := fun _ => ℕ) (r (Nat.succ i)) i (Nat.beq x q)) l i

theorem posOfA_spec (q : ℕ) : ∀ (l : List ℕ) (i : ℕ),
    posOfA q l i = 255 ∨ ∃ k < l.length, posOfA q l i = i + k ∧ l.getD k 0 = q
  | [], _ => Or.inl rfl
  | x :: l, i => by
    change Bool.rec (motive := fun _ => ℕ) (posOfA q l (i + 1)) i (Nat.beq x q) = 255 ∨
      ∃ k < (x :: l).length, Bool.rec (motive := fun _ => ℕ) (posOfA q l (i + 1)) i
        (Nat.beq x q) = i + k ∧ (x :: l).getD k 0 = q
    cases h : Nat.beq x q
    · change posOfA q l (i + 1) = 255 ∨ ∃ k < (x :: l).length, posOfA q l (i + 1) = i + k ∧
        (x :: l).getD k 0 = q
      rcases posOfA_spec q l (i + 1) with e | ⟨k, hk, e, hg⟩
      · exact Or.inl e
      · exact Or.inr ⟨k + 1, by simpa using hk, by omega, by simpa using hg⟩
    · right
      exact ⟨0, by simp, rfl, by simpa using h⟩

theorem posOf_get {q m : ℕ} {l : List ℕ} (hl : l.length ≤ 136) (h : posOf q l = m)
    (hm : m < l.length) : l.getD m 0 = q := by
  change posOfA q l 0 = m at h
  rcases posOfA_spec q l 0 with e | ⟨k, _, e, hg⟩
  · omega
  · rw [e] at h
    rw [← h, Nat.zero_add]
    exact hg

theorem posOf_lt (q : ℕ) (l : List ℕ) (hl : l.length ≤ 136) : posOf q l < 256 := by
  change posOfA q l 0 < 256
  rcases posOfA_spec q l 0 with e | ⟨k, hk, e, _⟩ <;> omega

theorem ofP_inj {p q : ℕ} (hp : p < 2 ^ 36) (hq : q < 2 ^ 36) (h : B6.ofP p = B6.ofP q) :
    p = q := by
  simp only [B6.ofP, B6.mk.injEq, Nat.shiftRight_eq_div_pow] at h
  norm_num at hp hq h
  omega

theorem ofP_id : B6.ofP 34630287489 = B6.id := by
  unfold B6.ofP B6.id
  norm_num [Nat.shiftRight_eq_div_pow]

theorem compP_eq (p q : ℕ) : compP p q = appQ p (q % 64) + 64 * appQ p ((q >>> 6) % 64) +
    4096 * appQ p ((q >>> 12) % 64) + 262144 * appQ p ((q >>> 18) % 64) +
    16777216 * appQ p ((q >>> 24) % 64) + 1073741824 * appQ p ((q >>> 30) % 64) := by
  unfold compP
  rw [land63, fldN_eq, fldN_eq, fldN_eq, fldN_eq, fldN_eq]
  have h0 := appQ_lt p (q % 64)
  have h1 := appQ_lt p ((q >>> 6) % 64)
  have h2 := appQ_lt p ((q >>> 12) % 64)
  have h3 := appQ_lt p ((q >>> 18) % 64)
  have h4 := appQ_lt p ((q >>> 24) % 64)
  generalize appQ p (q % 64) = a0 at h0 ⊢
  generalize appQ p ((q >>> 6) % 64) = a1 at h1 ⊢
  generalize appQ p ((q >>> 12) % 64) = a2 at h2 ⊢
  generalize appQ p ((q >>> 18) % 64) = a3 at h3 ⊢
  generalize appQ p ((q >>> 24) % 64) = a4 at h4 ⊢
  generalize appQ p ((q >>> 30) % 64) = a5
  change Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor a0 (Nat.shiftLeft a1 6))
    (Nat.shiftLeft a2 12)) (Nat.shiftLeft a3 18)) (Nat.shiftLeft a4 24)) (Nat.shiftLeft a5 30) = _
  rw [lor_sh (w := 6) (by norm_num; omega), lor_sh (w := 12) (by norm_num; omega),
    lor_sh (w := 18) (by norm_num; omega), lor_sh (w := 24) (by norm_num; omega),
    lor_sh (w := 30) (by norm_num; omega)]

theorem compP_lt (p q : ℕ) : compP p q < 2 ^ 36 := by
  have h0 := appQ_lt p (q % 64)
  have h1 := appQ_lt p ((q >>> 6) % 64)
  have h2 := appQ_lt p ((q >>> 12) % 64)
  have h3 := appQ_lt p ((q >>> 18) % 64)
  have h4 := appQ_lt p ((q >>> 24) % 64)
  have h5 := appQ_lt p ((q >>> 30) % 64)
  rw [compP_eq]
  norm_num
  omega

theorem ofP_compP (p q : ℕ) : B6.ofP (compP p q) = (B6.ofP p).comp (B6.ofP q) := by
  have e : (B6.ofP p).comp (B6.ofP q) = ⟨appQ p (q % 64), appQ p ((q >>> 6) % 64),
      appQ p ((q >>> 12) % 64), appQ p ((q >>> 18) % 64), appQ p ((q >>> 24) % 64),
      appQ p ((q >>> 30) % 64)⟩ := by
    simp only [B6.comp, appQ_eq]
    rfl
  have h0 := appQ_lt p (q % 64)
  have h1 := appQ_lt p ((q >>> 6) % 64)
  have h2 := appQ_lt p ((q >>> 12) % 64)
  have h3 := appQ_lt p ((q >>> 18) % 64)
  have h4 := appQ_lt p ((q >>> 24) % 64)
  have h5 := appQ_lt p ((q >>> 30) % 64)
  rw [e, compP_eq]
  generalize appQ p (q % 64) = a0 at h0 ⊢
  generalize appQ p ((q >>> 6) % 64) = a1 at h1 ⊢
  generalize appQ p ((q >>> 12) % 64) = a2 at h2 ⊢
  generalize appQ p ((q >>> 18) % 64) = a3 at h3 ⊢
  generalize appQ p ((q >>> 24) % 64) = a4 at h4 ⊢
  generalize appQ p ((q >>> 30) % 64) = a5 at h5 ⊢
  simp only [B6.ofP, B6.mk.injEq, Nat.shiftRight_eq_div_pow]
  norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem commP_iff {p q : ℕ} (hp : p < 2 ^ 36) (hq : q < 2 ^ 36) :
    commP p q = true ↔ (B6.ofP p).comp (B6.ofP q) = (B6.ofP q).comp (B6.ofP p) := by
  unfold commP
  rw [Nat.beq_eq]
  constructor
  · intro h
    rw [← ofP_compP, ← ofP_compP, h]
  · intro h
    apply ofP_inj (compP_lt p q) (compP_lt q p)
    rw [ofP_compP, ofP_compP, h]

theorem nbeq_false (x y : ℕ) : Nat.beq x y = false ↔ ¬ x = y := by
  rw [← Bool.not_eq_true, Nat.beq_eq]

theorem isInvP_eq {p : ℕ} (hp : p < 2 ^ 36) :
    isInvP p = ((B6.ofP p).comp (B6.ofP p) == B6.id && B6.ofP p != B6.id) := by
  change andB (Nat.beq (appQ p (Nat.land p 63)) 1) (andB (Nat.beq (appQ p (fldN p 6)) 2)
    (andB (Nat.beq (appQ p (fldN p 12)) 4) (andB (Nat.beq (appQ p (fldN p 18)) 8)
    (andB (Nat.beq (appQ p (fldN p 24)) 16) (andB (Nat.beq (appQ p (fldN p 30)) 32)
    (notB (Nat.beq p 34630287489))))))) = _
  rw [land63, fldN_eq, fldN_eq, fldN_eq, fldN_eq, fldN_eq]
  simp only [andB_eq, notB_eq]
  have e1 : (B6.ofP p).comp (B6.ofP p) = B6.id ↔ appQ p (p % 64) = 1 ∧
      appQ p ((p >>> 6) % 64) = 2 ∧ appQ p ((p >>> 12) % 64) = 4 ∧
      appQ p ((p >>> 18) % 64) = 8 ∧ appQ p ((p >>> 24) % 64) = 16 ∧
      appQ p ((p >>> 30) % 64) = 32 := by
    simp only [B6.comp, B6.id, B6.mk.injEq, appQ_eq]
    exact Iff.rfl
  have e2 : B6.ofP p = B6.id ↔ p = 34630287489 :=
    ⟨fun h => ofP_inj hp (by norm_num) (h.trans ofP_id.symm), fun h => h ▸ ofP_id⟩
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq, Nat.beq_eq,
    nbeq_false]
  rw [e1, e2]
  tauto

theorem allBelow_spec (f : ℕ → Bool) : ∀ n, allBelow f n = true → ∀ c < n, f c = true := by
  intro n
  induction n with
  | zero => intro _ c hc; omega
  | succ n ih =>
    intro h c hc
    change andB (f n) (allBelow f n) = true at h
    cases hf : f n
    · simp [andB, hf] at h
    · have h' : allBelow f n = true := by simpa [andB, hf] using h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact ih h' c hc
      · exact hf

theorem prmN_eq {T : ℕ} (hT : ∀ v < 64, fld T 3 v = oPts.idxOf (pn v) % 6) (p i : ℕ)
    (hi : i < 6) : prmN T p i = (permFn (B6.ofP p) ⟨i, hi⟩).val := by
  have ho : fld oPtsN 6 i = oPts.getD i 0 := by interval_cases i <;> rfl
  change fld T 3 (appQ p (fld oPtsN 6 i)) = _
  rw [ho, hT _ (appQ_lt _ _), appQ_eq]
  rfl

theorem exN_eq (i : ℕ) (hi : i < 6) : exN i = ex ⟨i, hi⟩ := by interval_cases i <;> rfl

theorem act4P_eq {T : ℕ} (hT : ∀ v < 64, fld T 3 v = oPts.idxOf (pn v) % 6) (p m : ℕ) :
    act4P T p m = act4 (permFn (B6.ofP p)) m := by
  have hb : ∀ j X, bit1 m j * X = if m.testBit j then X else 0 := fun j X => by
    rw [bit1_eq, Nat.mul_comm, CFSG.KS.S1277Gm.bit_mul]
    rfl
  have hx : ∀ i (hi : i < 6), exN (prmN T p i) = ex (permFn (B6.ofP p) ⟨i, hi⟩) :=
    fun i hi => by rw [prmN_eq hT p i hi]; exact exN_eq _ _
  change bit1 m 0 * (exN (prmN T p 0) ^^^ exN (prmN T p 1)) ^^^
    bit1 m 1 * (exN (prmN T p 0) ^^^ exN (prmN T p 2)) ^^^
    bit1 m 2 * (exN (prmN T p 0) ^^^ exN (prmN T p 3)) ^^^
    bit1 m 3 * (exN (prmN T p 0) ^^^ exN (prmN T p 4)) = _
  rw [hb, hb, hb, hb, hx 0 (by norm_num), hx 1 (by norm_num), hx 2 (by norm_num),
    hx 3 (by norm_num), hx 4 (by norm_num)]
  rfl

theorem testBit_fix4P {T : ℕ} (hT : ∀ v < 64, fld T 3 v = oPts.idxOf (pn v) % 6) (p c : ℕ)
    (hc : c < 16) : (fix4P T p).testBit c = (act4 (permFn (B6.ofP p)) c == c) := by
  change (maskBelow (fun m => Nat.beq (act4P T p m) m) 16).testBit c = _
  simp only [testBit_maskBelow, act4P_eq hT, hc, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, beq_iff_eq]

theorem fix4P_lt (T p : ℕ) : fix4P T p < 2 ^ 16 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    change (maskBelow (fun m => Nat.beq (act4P T p m) m) 16).testBit i = false
    have : ¬ i < 16 := by omega
    simp [testBit_maskBelow, this]

theorem fVl_eq (L : List B6) (m : ℕ) (hm : m < 2 ^ 64)
    (h : ∀ c < 64, m.testBit c = L.all fun B => B.app c == c) : fVl L = pcN m := by
  rw [pcN_eq m hm, pc64, fVl]
  congr 1
  apply List.filter_congr
  intro c hc
  exact (h c (List.mem_range.1 hc)).symm

theorem f4l_eq (L : List B6) (m : ℕ) (hm : m < 2 ^ 16)
    (h : ∀ c < 16, m.testBit c = L.all fun B => act4 (permFn B) c == c) : f4l L = pcN m := by
  rw [pcN_eq m (lt_trans hm (by norm_num)), pc64, f4l]
  have e : List.range 64 = List.range 16 ++ (List.range 48).map (16 + ·) := by
    rw [← List.range_add]
  have h0 : ((List.range 48).map (16 + ·)).filter (fun i => m.testBit i) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    simp [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
      (by omega : 16 ≤ 16 + y)))]
  rw [e, List.filter_append, List.length_append, h0, List.length_nil, Nat.add_zero]
  congr 1
  apply List.filter_congr
  intro c hc
  exact (h c (List.mem_range.1 hc)).symm

theorem invs6_eq {Q : List ℕ} (hN : nm6 = Q.map B6.ofP) (hb : ∀ p ∈ Q, p < 2 ^ 36) :
    invs6 = (Q.filter isInvP).map B6.ofP := by
  unfold invs6
  rw [hN, List.filter_map]
  apply congrArg
  apply List.filter_congr
  intro p hp
  exact (isInvP_eq (hb p hp)).symm

theorem getD_map' {l : List ℕ} {k : ℕ} (f : ℕ → ℕ) (hk : k < l.length) :
    (l.map f).getD k 0 = f (l.getD k 0) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem getD_mem {l : List ℕ} {k : ℕ} (hk : k < l.length) : l.getD k 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem iStep_spec (t : QT) (i : ℕ) (row : List ℕ) (h : iStep t i row = true) :
    pcN (fld t.fvN 64 i) * pcN (fld t.f4N 16 i) * 4 < 1024 ∧ ∀ j ∈ row,
      jStep t i (fld t.ipN 36 i) (fld t.fvN 64 i) (fld t.f4N 16 i) (fld t.cmN 136 i) row j =
        true := by
  unfold iStep at h
  simp only [strictB_ml] at h
  change andB (Nat.blt (pcN (fld t.fvN 64 i) * pcN (fld t.f4N 16 i) * 4) 1024)
    (allL (jStep t i (fld t.ipN 36 i) (fld t.fvN 64 i) (fld t.f4N 16 i) (fld t.cmN 136 i) row)
      row) = true at h
  rw [andB_eq, allL_eq, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at h
  exact h

theorem jStep_spec (t : QT) (i pi vi wi ci : ℕ) (row : List ℕ) (j : ℕ)
    (h : jStep t i pi vi wi ci row j = true) (hne : fld t.ipN 36 j ≠ pi) :
    ptQ t i j < t.n ∧ pcN (vi &&& fld t.fvN 64 j) * pcN (wi &&& fld t.f4N 16 j) * 16 < 1024 ∧
      ∀ k ∈ row, (ci &&& fld t.cmN 136 j).testBit k = true →
        kStep t i j (ptQ t i j) pi (fld t.ipN 36 j) (fld t.ipN 36 (ptQ t i j))
          (vi &&& fld t.fvN 64 j) (wi &&& fld t.f4N 16 j) (ci &&& fld t.cmN 136 j) k = true := by
  unfold jStep at h
  simp only [strictB_ml] at h
  change orB (Nat.beq (fld t.ipN 36 j) pi) (andB (Nat.blt (ptQ t i j) t.n)
    (andB (Nat.blt (pcN (vi &&& fld t.fvN 64 j) * pcN (wi &&& fld t.f4N 16 j) * 16) 1024)
    (allL (fun k => orB (notB (bitN (ci &&& fld t.cmN 136 j) k))
      (kStep t i j (ptQ t i j) pi (fld t.ipN 36 j) (fld t.ipN 36 (ptQ t i j))
        (vi &&& fld t.fvN 64 j) (wi &&& fld t.f4N 16 j) (ci &&& fld t.cmN 136 j) k)) row))) =
    true at h
  simp only [orB_eq, andB_eq, allL_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq,
    List.all_eq_true, Nat.beq_eq] at h
  rcases h with h | ⟨h1, h2, h3⟩
  · exact absurd h hne
  · refine ⟨h1, h2, fun k hk hb => ?_⟩
    have := h3 k hk
    rw [notB_eq, bitN_eq, hb, Bool.not_true] at this
    rcases this with h | h
    · exact absurd h (by decide)
    · exact h

theorem kStep_spec (t : QT) (i j kij pi pj pij vij wij cij k : ℕ)
    (h : kStep t i j kij pi pj pij vij wij cij k = true) (h1 : fld t.ipN 36 k ≠ pi)
    (h2 : fld t.ipN 36 k ≠ pj) (h3 : fld t.ipN 36 k ≠ pij)
    (h4 : fld t.ipN 36 k ≠ 34630287489) :
    pcN (vij &&& fld t.fvN 64 k) * pcN (wij &&& fld t.f4N 16 k) * 64 < 1024 ∧
      (cij &&& fld t.cmN 136 k) &&& (1 <<< i ||| 1 <<< j ||| 1 <<< kij ||| 1 <<< k |||
        1 <<< ptQ t i k ||| 1 <<< ptQ t j k ||| 1 <<< ptQ t kij k) =
        (cij &&& fld t.cmN 136 k) := by
  unfold kStep at h
  simp only [strictB_ml] at h
  change orB (Nat.beq (fld t.ipN 36 k) pi) (orB (Nat.beq (fld t.ipN 36 k) pj)
    (orB (Nat.beq (fld t.ipN 36 k) pij) (orB (Nat.beq (fld t.ipN 36 k) 34630287489)
    (andB (Nat.blt (pcN (vij &&& fld t.fvN 64 k) * pcN (wij &&& fld t.f4N 16 k) * 64) 1024)
    (Nat.beq ((cij &&& fld t.cmN 136 k) &&& (1 <<< i ||| 1 <<< j ||| 1 <<< kij ||| 1 <<< k |||
        1 <<< ptQ t i k ||| 1 <<< ptQ t j k ||| 1 <<< ptQ t kij k))
        (cij &&& fld t.cmN 136 k)))))) = true at h
  simp only [orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  rcases h with h | h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact absurd h h4
  · exact h

theorem allRows_spec (t : QT) : ∀ (R : List (List ℕ)) (i : ℕ), allRows t R i = true →
    ∀ k < R.length, iStep t (i + k) (R.getD k []) = true
  | [], _, _, k, hk => absurd hk (by simp)
  | row :: R, i, h, k, hk => by
    change andB (iStep t i row) (allRows t R (i + 1)) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := allRows_spec t R (i + 1) h.2 k (by simpa using hk)
      rw [List.getD_cons_succ]
      have e : i + (k + 1) = i + 1 + k := by omega
      rw [e]
      exact this

noncomputable def rowsA (cmN n : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  Nat.rec (motive := fun _ => List (List ℕ) → List (List ℕ)) (fun acc => acc)
    (fun i r acc => r (bitsBelow (fld cmN (nat_lit 136) i) (nat_lit 136) [] :: acc)) n acc

theorem rowsA_eq (cmN : ℕ) : ∀ n acc,
    rowsA cmN n acc = (List.range n).map (fun i => bitsBelow (fld cmN 136 i) 136 []) ++ acc
  | 0, acc => by simp [rowsA]
  | n + 1, acc => by
    change rowsA cmN n (bitsBelow (fld cmN 136 n) 136 [] :: acc) = _
    rw [rowsA_eq cmN n, List.range_succ, List.map_append, List.append_assoc]
    rfl

theorem rowsOf_eq (cmN n : ℕ) :
    rowsOf cmN n = (List.range n).map (fun i => bitsBelow (fld cmN 136 i) 136 []) := by
  change rowsA cmN n [] = _
  rw [rowsA_eq, List.append_nil]

set_option exponentiation.threshold 2000 in
theorem fld_nest (T x y : ℕ) (hy : y < 136) : fld T 8 (136 * x + y) = fld (fld T 1088 x) 8 y := by
  have e1 : 8 * (136 * x + y) = 1088 * x + 8 * y := by ring
  have e2 : (2 : ℕ) ^ 1088 = 2 ^ (8 * y) * 2 ^ (1088 - 8 * y) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [fld_eq, fld_eq, fld_eq, e1, Nat.pow_add, ← Nat.div_div_eq_div_mul, e2,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

set_option exponentiation.threshold 2000 in
theorem ptQ_spec (IP : List ℕ) (CM : ℕ) (hl : IP.length ≤ 136) (t : QT)
    (ht : t.ptN = ptAll IP CM) {x y l : ℕ} (hx : x < IP.length) (hy : y < IP.length)
    (hl' : l < IP.length) (h : ptQ t x y = l) :
    IP.getD l 0 = compP (IP.getD x 0) (IP.getD y 0) := by
  have hg8 : ∀ p cm, ∀ q j,
      (Bool.rec (motive := fun _ => ℕ) 255 (posOf (compP p q) IP) (bitN cm j) : ℕ) < 2 ^ 8 := by
    intro p cm q j
    cases bitN cm j
    · norm_num
    · exact (posOf_lt _ IP hl).trans_le (by norm_num)
  have hrow : ∀ p i, ptRow IP p (fld CM 136 i) < 2 ^ 1088 := fun p i => by
    change recP 8 (fun q j => Bool.rec (motive := fun _ => ℕ) 255 (posOf (compP p q) IP)
      (bitN (fld CM 136 i) j)) IP 0 < _
    exact (recP_lt (hg8 p _) IP 0).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  change fld t.ptN 8 (136 * x + y) = l at h
  rw [fld_nest _ _ _ (by omega), ht] at h
  have e1 : fld (ptAll IP CM) 1088 x = ptRow IP (IP.getD x 0) (fld CM 136 x) := by
    change fld (recP 1088 (fun p i => ptRow IP p (fld CM 136 i)) IP 0) 1088 x = _
    rw [recP_fld hrow IP 0 x hx, Nat.zero_add]
  have e2 : fld (ptRow IP (IP.getD x 0) (fld CM 136 x)) 8 y =
      Bool.rec (motive := fun _ => ℕ) 255 (posOf (compP (IP.getD x 0) (IP.getD y 0)) IP)
        (bitN (fld CM 136 x) y) := by
    change fld (recP 8 (fun q j => Bool.rec (motive := fun _ => ℕ) 255
      (posOf (compP (IP.getD x 0) q) IP) (bitN (fld CM 136 x) j)) IP 0) 8 y = _
    rw [recP_fld (hg8 _ _) IP 0 y hy, Nat.zero_add]
  rw [e1, e2] at h
  cases hbit : bitN (fld CM 136 x) y
  · rw [hbit] at h
    change 255 = l at h
    omega
  · rw [hbit] at h
    change posOf _ IP = l at h
    exact posOf_get hl h hl'

theorem allBelow_of (f : ℕ → Bool) : ∀ n, (∀ c < n, f c = true) → allBelow f n = true
  | 0, _ => rfl
  | n + 1, h => by
    change andB (f n) (allBelow f n) = true
    rw [andB_eq, h n (by omega), allBelow_of f n (fun c hc => h c (by omega))]
    rfl

theorem id_app (v : ℕ) (hv : v < 64) : B6.id.app v = v := by
  revert v
  decide

theorem id_comp_ofP (p : ℕ) : B6.id.comp (B6.ofP p) = B6.ofP p := by
  have h : ∀ x, B6.id.app (x % 64) = x % 64 := fun x => id_app _ (Nat.mod_lt _ (by norm_num))
  simp only [B6.comp, B6.ofP, h]

theorem tab_sound (T : ℕ) (hT : ∀ v < 64, fld T 3 v = oPts.idxOf (pn v) % 6) (IP : List ℕ)
    (hl : IP.length ≤ 136) (hIb : ∀ p ∈ IP, p < 2 ^ 36) (t : QT) (hn : t.n = IP.length)
    (hip : t.ipN = packL 36 IP) (hfv : t.fvN = packL 64 (IP.map fixMP))
    (hf4 : t.f4N = packL 16 (IP.map (fix4P T)))
    (hcm : t.cmN = packL 136 (IP.map fun p => posMask (commP p) IP))
    (hpt : t.ptN = ptAll IP t.cmN) (hR : allRows t (rowsOf t.cmN t.n) 0 = true) :
    (∀ a ∈ IP.map B6.ofP, fVl [a] * f4l [a] * 4 < 1024) ∧
    (∀ a ∈ IP.map B6.ofP, ∀ b ∈ IP.map B6.ofP, a.comp b = b.comp a → b ≠ a →
      fVl [a, b] * f4l [a, b] * 16 < 1024) ∧
    (∀ a ∈ IP.map B6.ofP, ∀ b ∈ IP.map B6.ofP, a.comp b = b.comp a → b ≠ a →
      ∀ c ∈ IP.map B6.ofP, a.comp c = c.comp a → b.comp c = c.comp b → c ∉ span2 a b →
        fVl [a, b, c] * f4l [a, b, c] * 64 < 1024) ∧
    (∀ a ∈ IP.map B6.ofP, ∀ b ∈ IP.map B6.ofP, a.comp b = b.comp a → b ≠ a →
      ∀ c ∈ IP.map B6.ofP, a.comp c = c.comp a → b.comp c = c.comp b → c ∉ span2 a b →
      ∀ d ∈ IP.map B6.ofP, a.comp d = d.comp a → b.comp d = d.comp b → c.comp d = d.comp c →
        d ∈ span3 a b c) := by
  have hmem : ∀ B ∈ IP.map B6.ofP, ∃ i < IP.length, B = B6.ofP (IP.getD i 0) := by
    intro B hB
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hB
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hp
    exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi, e]⟩
  have hPb : ∀ k < IP.length, IP.getD k 0 < 2 ^ 36 := fun k hk => hIb _ (getD_mem hk)
  have fI : ∀ k < IP.length, fld t.ipN 36 k = IP.getD k 0 := fun k hk => by
    rw [hip]
    exact packL_fld IP hIb k hk
  have fV : ∀ k < IP.length, fld t.fvN 64 k = fixMP (IP.getD k 0) := fun k hk => by
    rw [hfv, packL_fld _ (fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      exact fixMP_lt p) k (by simpa using hk), getD_map' _ hk]
  have fW : ∀ k < IP.length, fld t.f4N 16 k = fix4P T (IP.getD k 0) := fun k hk => by
    rw [hf4, packL_fld _ (fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      exact fix4P_lt T p) k (by simpa using hk), getD_map' _ hk]
  have fC : ∀ k < IP.length, fld t.cmN 136 k = posMask (commP (IP.getD k 0)) IP := fun k hk => by
    rw [hcm, packL_fld _ (fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      exact posMask_lt _ IP hl) k (by simpa using hk), getD_map' _ hk]
  have fP : ∀ x < IP.length, ∀ y < IP.length, ∀ l < IP.length, ptQ t x y = l →
      IP.getD l 0 = compP (IP.getD x 0) (IP.getD y 0) :=
    fun x hx y hy l hl' h => ptQ_spec IP t.cmN hl t hpt hx hy hl' h
  have hS : ∀ i < IP.length, iStep t i (bitsBelow (fld t.cmN 136 i) 136 []) = true := by
    intro i hi
    have hlen : i < (rowsOf t.cmN t.n).length := by
      rw [rowsOf_eq, hn]
      simpa using hi
    have := allRows_spec t _ 0 hR i hlen
    have e : ((List.range t.n).map (fun i => bitsBelow (fld t.cmN 136 i) 136 [])).getD i [] =
        bitsBelow (fld t.cmN 136 i) 136 [] := by
      simp [List.getD_eq_getElem?_getD, hn, hi]
    rw [rowsOf_eq, e, Nat.zero_add] at this
    exact this
  have hcmb : ∀ x < IP.length, ∀ y < IP.length, ((fld t.cmN 136 x).testBit y = true ↔
      (B6.ofP (IP.getD x 0)).comp (B6.ofP (IP.getD y 0)) =
        (B6.ofP (IP.getD y 0)).comp (B6.ofP (IP.getD x 0))) := by
    intro x hx y hy
    rw [fC x hx, testBit_posMask, commP_iff (hPb x hx) (hPb y hy)]
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have hrow : ∀ x < IP.length, ∀ y < IP.length, (fld t.cmN 136 x).testBit y = true →
      y ∈ bitsBelow (fld t.cmN 136 x) 136 [] := by
    intro x hx y hy h
    rw [bitsBelow_eq, List.append_nil, List.mem_filter, List.mem_range]
    exact ⟨by omega, h⟩
  have hV : ∀ k < IP.length, ∀ c < 64,
      (fld t.fvN 64 k).testBit c = ((B6.ofP (IP.getD k 0)).app c == c) := by
    intro k hk c hc
    rw [fV k hk]
    apply Bool.eq_iff_iff.2
    rw [testBit_fixMP, beq_iff_eq]
    exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
  have hW : ∀ k < IP.length, ∀ c < 16,
      (fld t.f4N 16 k).testBit c = (act4 (permFn (B6.ofP (IP.getD k 0))) c == c) := by
    intro k hk c hc
    rw [fW k hk, testBit_fix4P hT _ _ hc]
  have hVlt : ∀ k < IP.length, fld t.fvN 64 k < 2 ^ 64 := fun k hk => by
    rw [fV k hk]
    exact fixMP_lt _
  have hWlt : ∀ k < IP.length, fld t.f4N 16 k < 2 ^ 16 := fun k hk => by
    rw [fW k hk]
    exact fix4P_lt _ _
  have hpair : ∀ i < IP.length, ∀ j < IP.length,
      (B6.ofP (IP.getD i 0)).comp (B6.ofP (IP.getD j 0)) =
        (B6.ofP (IP.getD j 0)).comp (B6.ofP (IP.getD i 0)) →
      B6.ofP (IP.getD j 0) ≠ B6.ofP (IP.getD i 0) →
      ptQ t i j < IP.length ∧
      pcN (fld t.fvN 64 i &&& fld t.fvN 64 j) * pcN (fld t.f4N 16 i &&& fld t.f4N 16 j) * 16 <
        1024 ∧
      ∀ k ∈ bitsBelow (fld t.cmN 136 i) 136 [],
        (fld t.cmN 136 i &&& fld t.cmN 136 j).testBit k = true →
        kStep t i j (ptQ t i j) (fld t.ipN 36 i) (fld t.ipN 36 j) (fld t.ipN 36 (ptQ t i j))
          (fld t.fvN 64 i &&& fld t.fvN 64 j) (fld t.f4N 16 i &&& fld t.f4N 16 j)
          (fld t.cmN 136 i &&& fld t.cmN 136 j) k = true := by
    intro i hi j hj hab hne
    have hJ := (iStep_spec t i _ (hS i hi)).2 j (hrow i hi j hj ((hcmb i hi j hj).2 hab))
    have hne' : fld t.ipN 36 j ≠ fld t.ipN 36 i := by
      rw [fI j hj, fI i hi]
      intro e
      exact hne (by rw [e])
    have := jStep_spec t i _ _ _ _ _ j hJ hne'
    rw [hn] at this
    exact this
  have htri : ∀ i < IP.length, ∀ j < IP.length, ∀ k < IP.length,
      (B6.ofP (IP.getD i 0)).comp (B6.ofP (IP.getD j 0)) =
        (B6.ofP (IP.getD j 0)).comp (B6.ofP (IP.getD i 0)) →
      B6.ofP (IP.getD j 0) ≠ B6.ofP (IP.getD i 0) →
      (B6.ofP (IP.getD i 0)).comp (B6.ofP (IP.getD k 0)) =
        (B6.ofP (IP.getD k 0)).comp (B6.ofP (IP.getD i 0)) →
      (B6.ofP (IP.getD j 0)).comp (B6.ofP (IP.getD k 0)) =
        (B6.ofP (IP.getD k 0)).comp (B6.ofP (IP.getD j 0)) →
      B6.ofP (IP.getD k 0) ∉ span2 (B6.ofP (IP.getD i 0)) (B6.ofP (IP.getD j 0)) →
      ptQ t i j < IP.length ∧
      pcN ((fld t.fvN 64 i &&& fld t.fvN 64 j) &&& fld t.fvN 64 k) *
        pcN ((fld t.f4N 16 i &&& fld t.f4N 16 j) &&& fld t.f4N 16 k) * 64 < 1024 ∧
      ((fld t.cmN 136 i &&& fld t.cmN 136 j) &&& fld t.cmN 136 k) &&&
        (1 <<< i ||| 1 <<< j ||| 1 <<< ptQ t i j ||| 1 <<< k ||| 1 <<< ptQ t i k |||
          1 <<< ptQ t j k ||| 1 <<< ptQ t (ptQ t i j) k) =
        ((fld t.cmN 136 i &&& fld t.cmN 136 j) &&& fld t.cmN 136 k) := by
    intro i hi j hj k hk hab hne hac hbc hsp
    obtain ⟨hkij, -, hK⟩ := hpair i hi j hj hab hne
    simp only [span2, List.mem_cons, List.not_mem_nil, or_false, not_or] at hsp
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hsp
    have hcij : (fld t.cmN 136 i &&& fld t.cmN 136 j).testBit k = true := by
      rw [Nat.testBit_and, Bool.and_eq_true]
      exact ⟨(hcmb i hi k hk).2 hac, (hcmb j hj k hk).2 hbc⟩
    have hks := hK k (hrow i hi k hk ((hcmb i hi k hk).2 hac)) hcij
    have hPij := fP i hi j hj _ hkij rfl
    have := kStep_spec t _ _ _ _ _ _ _ _ _ k hks
      (by rw [fI k hk, fI i hi]; intro e; exact hs2 (by rw [e]))
      (by rw [fI k hk, fI j hj]; intro e; exact hs3 (by rw [e]))
      (by
        rw [fI k hk, fI _ hkij, hPij]
        intro e
        exact hs4 (by rw [e, ofP_compP]))
      (by rw [fI k hk]; intro e; exact hs1 (by rw [e, ofP_id]))
    exact ⟨hkij, this⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := hmem a ha
    have h2 := (iStep_spec t i _ (hS i hi)).1
    rw [fVl_eq _ _ (hVlt i hi) (fun c hc => by rw [hV i hi c hc]; simp),
      f4l_eq _ _ (hWlt i hi) (fun c hc => by rw [hW i hi c hc]; simp)]
    exact h2
  · intro a ha b hb hab hne
    obtain ⟨i, hi, rfl⟩ := hmem a ha
    obtain ⟨j, hj, rfl⟩ := hmem b hb
    have h3 := (hpair i hi j hj hab hne).2.1
    rw [fVl_eq _ (fld t.fvN 64 i &&& fld t.fvN 64 j) (lt_of_le_of_lt Nat.and_le_left (hVlt i hi))
        (fun c hc => by rw [Nat.testBit_and, hV i hi c hc, hV j hj c hc]; simp),
      f4l_eq _ (fld t.f4N 16 i &&& fld t.f4N 16 j) (lt_of_le_of_lt Nat.and_le_left (hWlt i hi))
        (fun c hc => by rw [Nat.testBit_and, hW i hi c hc, hW j hj c hc]; simp)]
    exact h3
  · intro a ha b hb hab hne c hc hac hbc hsp
    obtain ⟨i, hi, rfl⟩ := hmem a ha
    obtain ⟨j, hj, rfl⟩ := hmem b hb
    obtain ⟨k, hk, rfl⟩ := hmem c hc
    have h4 := (htri i hi j hj k hk hab hne hac hbc hsp).2.1
    rw [fVl_eq _ ((fld t.fvN 64 i &&& fld t.fvN 64 j) &&& fld t.fvN 64 k)
        (lt_of_le_of_lt Nat.and_le_left (lt_of_le_of_lt Nat.and_le_left (hVlt i hi)))
        (fun c hc => by
          rw [Nat.testBit_and, Nat.testBit_and, hV i hi c hc, hV j hj c hc, hV k hk c hc]
          simp [Bool.and_assoc]),
      f4l_eq _ ((fld t.f4N 16 i &&& fld t.f4N 16 j) &&& fld t.f4N 16 k)
        (lt_of_le_of_lt Nat.and_le_left (lt_of_le_of_lt Nat.and_le_left (hWlt i hi)))
        (fun c hc => by
          rw [Nat.testBit_and, Nat.testBit_and, hW i hi c hc, hW j hj c hc, hW k hk c hc]
          simp [Bool.and_assoc])]
    exact h4
  · intro a ha b hb hab hne c hc hac hbc hsp d hd had hbd hcd
    obtain ⟨i, hi, rfl⟩ := hmem a ha
    obtain ⟨j, hj, rfl⟩ := hmem b hb
    obtain ⟨k, hk, rfl⟩ := hmem c hc
    obtain ⟨l, hl', rfl⟩ := hmem d hd
    obtain ⟨hkij, -, hM⟩ := htri i hi j hj k hk hab hne hac hbc hsp
    have hX : ((fld t.cmN 136 i &&& fld t.cmN 136 j) &&& fld t.cmN 136 k).testBit l = true := by
      rw [Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨(hcmb i hi l hl').2 had, (hcmb j hj l hl').2 hbd⟩, (hcmb k hk l hl').2 hcd⟩
    have hb := congrArg (fun m => Nat.testBit m l) hM
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow] at hb
    rw [Nat.testBit_and, Nat.testBit_and] at hX
    rw [hX, Bool.true_and] at hb
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
    have hPij := fP i hi j hj _ hkij rfl
    rcases hb with ((((((e | e) | e) | e) | e) | e) | e)
    · rw [← e]
      simp [span3, span2]
    · rw [← e]
      simp [span3, span2]
    · rw [← e, hPij, ofP_compP]
      simp [span3, span2]
    · rw [← e]
      have : B6.id.comp (B6.ofP (IP.getD k 0)) ∈ span3 (B6.ofP (IP.getD i 0))
          (B6.ofP (IP.getD j 0)) (B6.ofP (IP.getD k 0)) := by simp [span3, span2]
      rwa [id_comp_ofP] at this
    · rw [fP i hi k hk l hl' e, ofP_compP]
      simp [span3, span2]
    · rw [fP j hj k hk l hl' e, ofP_compP]
      simp [span3, span2]
    · rw [fP _ hkij k hk l hl' e, ofP_compP, hPij, ofP_compP]
      simp [span3, span2]

open CFSG.Quasithin.H13.S127.Mod in
theorem qChk_sound (T : ℕ) (Q : List ℕ) (hN : nm6 = Q.map B6.ofP)
    (hT : ∀ v < 64, fld T 3 v = oPts.idxOf (pn v) % 6) (h : qChk T Q = true) :

    (∀ B ∈ nm6, (∀ i : Fin 6, permFn B i = i) → B ∈ zs6) ∧
    (∀ a ∈ invs6, fVl [a] * f4l [a] * 4 < 1024) ∧
    (∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a →
      fVl [a, b] * f4l [a, b] * 16 < 1024) ∧
    (∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a → ∀ c ∈ invs6,
      a.comp c = c.comp a → b.comp c = c.comp b → c ∉ span2 a b →
        fVl [a, b, c] * f4l [a, b, c] * 64 < 1024) ∧
    (∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a → ∀ c ∈ invs6,
      a.comp c = c.comp a → b.comp c = c.comp b → c ∉ span2 a b → ∀ d ∈ invs6,
        a.comp d = d.comp a → b.comp d = d.comp b → c.comp d = d.comp c → d ∈ span3 a b c) := by
  unfold qChk at h
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hk, hl, hq⟩ := h
  rw [filtL_eq] at hl hq
  change Nat.ble (List.length (Q.filter isInvP)) 136 = true at hl
  rw [Nat.ble_eq] at hl
  unfold kerChk at hk
  rw [allL_eq, List.all_eq_true] at hk
  have hK : ∀ p ∈ Q, p < 2 ^ 36 ∧ (fix6 T p = false ∨ memZ p = true) := by
    intro p hp
    have := hk p hp
    change andB (Nat.blt p 68719476736) (orB (notB (fix6 T p)) (memZ p)) = true at this
    rw [andB_eq, orB_eq, notB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq,
      Bool.not_eq_true'] at this
    exact ⟨by norm_num; exact this.1, this.2⟩
  have hb : ∀ p ∈ Q, p < 2 ^ 36 := fun p hp => (hK p hp).1
  have hI := invs6_eq hN hb
  refine ⟨?_, ?_⟩
  · intro B hB hfix
    rw [hN] at hB
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hB
    rcases (hK p hp).2 with h6 | hz
    · have : fix6 T p = true := by
        apply allBelow_of
        intro c hc
        rw [Nat.beq_eq, prmN_eq hT p c hc, hfix ⟨c, hc⟩]
      rw [this] at h6
      exact absurd h6 (by decide)
    · change orB (Nat.beq p 34630287489) (orB (Nat.beq p 52079657154)
        (Nat.beq p 17986273347)) = true at hz
      simp only [orB_eq, Bool.or_eq_true, Nat.beq_eq] at hz
      have ez : zs6 = [B6.ofP 34630287489, B6.ofP 52079657154, B6.ofP 17986273347] := rfl
      rw [ez]
      rcases hz with rfl | rfl | rfl <;> simp
  · rw [hI]
    have hIb : ∀ p ∈ Q.filter isInvP, p < 2 ^ 36 := fun p hp => hb p (List.mem_filter.1 hp).1
    have hR : allRows ⟨(Q.filter isInvP).length, packL 36 (Q.filter isInvP),
        packL 64 ((Q.filter isInvP).map fixMP), packL 16 ((Q.filter isInvP).map (fix4P T)),
        packL 136 ((Q.filter isInvP).map fun p => posMask (commP p) (Q.filter isInvP)),
        ptAll (Q.filter isInvP)
          (packL 136 ((Q.filter isInvP).map fun p => posMask (commP p) (Q.filter isInvP)))⟩
        (rowsOf (packL 136 ((Q.filter isInvP).map fun p => posMask (commP p) (Q.filter isInvP)))
          (Q.filter isInvP).length) 0 = true := by
      unfold qChkI qTab at hq
      simp only [strictB_ml, andB_eq, Bool.and_eq_true] at hq
      exact hq.2
    exact tab_sound T hT _ hl hIb _ rfl rfl rfl rfl rfl rfl hR

end CFSG.KS.S1277Q

end
