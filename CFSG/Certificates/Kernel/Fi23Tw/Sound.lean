module

public import Certificates.Data.Kernel.Fi23Tw.Defs
public import CFSG.Certificates.Kernel.Fi23Y322.Sound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.Fi23Tw

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KC.Fi23Y322 CFSG.KS.Raw.Orb

theorem bitB_eq (A k : Nat) : bitB A k = A.testBit k := by
  unfold bitB
  have e : Nat.land (Nat.shiftRight A k) 1 = A / 2 ^ k % 2 := by
    change (A >>> k) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (A / 2 ^ k) with h | h <;> rw [h] <;> rfl

theorem nthL_eq : ∀ (L : List Nat) (i : Nat), nthL L i = L.getD i 0
  | [], _ => rfl
  | a :: L, i => by
    have e : nthL (a :: L) i = nIf(Nat.beq i (nat_lit 0), a, nthL L (Nat.pred i)) := rfl
    rw [e, nIf_eq]
    cases i with
    | zero => rfl
    | succ i =>
      have h1 : Nat.beq (i + 1) 0 = false := rfl
      rw [h1, if_neg (by decide)]
      change nthL L i = L.getD i 0
      exact nthL_eq L i

theorem dropL_eq : ∀ (L : List Nat) (i : Nat), dropL L i = L.drop i
  | [], i => by cases i <;> rfl
  | a :: L, 0 => rfl
  | a :: L, i + 1 => by
    have e : dropL (a :: L) (i + 1) = dropL L i := rfl
    rw [e, dropL_eq L i]
    rfl

theorem getD_drop (L : List Nat) (n t : Nat) : (L.drop n).getD t 0 = L.getD (n + t) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem rowK_spec {G : Nat → Nat} {A a i : Nat} :
    ∀ (T : List Nat) (j : Nat), rowK G A a i T j = true → ∀ t < T.length,
      A.testBit (135 * i + (j + t)) = cmK G a (T.getD t 0) ∧
        A.testBit (135 * (j + t) + i) = cmK G a (T.getD t 0)
  | [], _, _, t, ht => absurd ht (by simp)
  | b :: T, j, h, t, ht => by
    have e : rowK G A a i (b :: T) j = bAnd(bIf(cmK G a b,
        bAnd(bitB A (Nat.add (Nat.mul (nat_lit 135) i) j),
          bitB A (Nat.add (Nat.mul (nat_lit 135) j) i)),
        bAnd(Bool.not (bitB A (Nat.add (Nat.mul (nat_lit 135) i) j)),
          Bool.not (bitB A (Nat.add (Nat.mul (nat_lit 135) j) i)))),
      rowK G A a i T (Nat.succ j)) := rfl
    rw [e, bAnd_eq, bIf_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases t with
    | zero =>
      simp only [bitB_eq, Nat.add_zero, List.getD_cons_zero] at h1 ⊢
      change A.testBit (135 * i + j) = cmK G a b ∧ A.testBit (135 * j + i) = cmK G a b
      by_cases hc : cmK G a b = true
      · rw [if_pos hc, Bool.and_eq_true] at h1
        change A.testBit (135 * i + j) = true ∧ A.testBit (135 * j + i) = true at h1
        rw [hc]
        exact h1
      · rw [if_neg hc, Bool.and_eq_true] at h1
        change (!A.testBit (135 * i + j)) = true ∧ (!A.testBit (135 * j + i)) = true at h1
        rw [Bool.eq_false_iff.2 hc]
        simpa using h1
    | succ t =>
      have ht' : t < T.length := by simpa using ht
      have h3 := rowK_spec T (Nat.succ j) h2 t ht'
      rw [List.getD_cons_succ]
      have e2 : j + (t + 1) = Nat.succ j + t := by omega
      rw [e2]
      exact h3

theorem matK_spec {G : Nat → Nat} {A : Nat} {F : List Nat} {lo c : Nat}
    (h : matK G A F lo c = true) : ∀ i, lo ≤ i → i < lo + c → ∀ j, i < j → j < F.length →
      A.testBit (135 * i + j) = cmK G (F.getD i 0) (F.getD j 0) ∧
        A.testBit (135 * j + i) = cmK G (F.getD i 0) (F.getD j 0) := by
  intro i hi1 hi2 j hj1 hj2
  unfold matK at h
  have h1 := allN_iff.1 h (i - lo) (by omega)
  rw [strictB_eq] at h1
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, nthL_eq, dropL_eq] at h1
  have h2 := rowK_spec (F.drop (Nat.succ i)) (Nat.succ i) h1 (j - (i + 1))
    (by rw [List.length_drop]; omega)
  have e2 : Nat.succ i + (j - (i + 1)) = j := by omega
  rw [getD_drop, e2] at h2
  exact h2

theorem twLoop_spec {A : Nat} : ∀ (n m : Nat) (P : List Nat), twLoop A n m P = true →
    (∀ e ∈ P, m ≤ e % 32768 ∧ e % 32768 < m + n) ∧
      ∀ m', m ≤ m' → m' < m + n → (twB A m' = true ↔ ∃ e ∈ P, e % 32768 = m')
  | 0, m, P, h => by
    cases P with
    | nil => exact ⟨fun e he => absurd he List.not_mem_nil, fun m' h1 h2 => by omega⟩
    | cons e P => exact absurd h (by intro h'; cases h')
  | n + 1, m, P, h => by
    have hl : ∀ e : Nat, Nat.land e (nat_lit 32767) = e % 32768 := fun e => by
      change e &&& 32767 = _
      rw [show (32767 : Nat) = 2 ^ 15 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have eq0 : twLoop A (n + 1) m P = strictB m fun m => List.rec (motive := fun _ => Bool)
        (bAnd(Bool.not (twB A m), twLoop A n (Nat.succ m) P))
        (fun e P' _ => bIf(Nat.beq (Nat.land e (nat_lit 32767)) m,
          bAnd(twB A m, twLoop A n (Nat.succ m) P'),
          bAnd(Bool.not (twB A m), twLoop A n (Nat.succ m) P))) P := rfl
    rw [eq0, strictB_eq] at h
    cases P with
    | nil =>
      rw [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨-, ih⟩ := twLoop_spec n (m + 1) [] h2
      refine ⟨fun e he => absurd he List.not_mem_nil, fun m' hm1 hm2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hm1 with rfl | hm1
      · simp [h1]
      · exact ih m' hm1 (by omega)
    | cons e P' =>
      change bIf(Nat.beq (Nat.land e (nat_lit 32767)) m,
          bAnd(twB A m, twLoop A n (Nat.succ m) P'),
          bAnd(Bool.not (twB A m), twLoop A n (Nat.succ m) (e :: P'))) = true at h
      rw [bIf_eq, bAnd_eq, bAnd_eq, hl] at h
      by_cases he : Nat.beq (e % 32768) m = true
      · rw [if_pos he, Bool.and_eq_true] at h
        have hem : e % 32768 = m := Nat.eq_of_beq_eq_true he
        obtain ⟨h1, h2⟩ := h
        obtain ⟨ihP, ih⟩ := twLoop_spec n (m + 1) P' h2
        refine ⟨fun e' he' => ?_, fun m' hm1 hm2 => ?_⟩
        · rcases List.mem_cons.1 he' with rfl | he'
          · omega
          · have := ihP e' he'
            omega
        · rcases Nat.eq_or_lt_of_le hm1 with rfl | hm1
          · exact ⟨fun _ => ⟨e, List.mem_cons_self, hem⟩, fun _ => h1⟩
          · rw [ih m' hm1 (by omega)]
            constructor
            · rintro ⟨e', he', h'⟩
              exact ⟨e', List.mem_cons_of_mem e he', h'⟩
            · rintro ⟨e', he', h'⟩
              rcases List.mem_cons.1 he' with rfl | he'
              · omega
              · exact ⟨e', he', h'⟩
      · rw [if_neg he, Bool.and_eq_true, Bool.not_eq_true'] at h
        have hem : e % 32768 ≠ m := fun h' => he (by rw [h']; exact Nat.beq_refl m)
        obtain ⟨h1, h2⟩ := h
        obtain ⟨ihP, ih⟩ := twLoop_spec n (m + 1) (e :: P') h2
        refine ⟨fun e' he' => ?_, fun m' hm1 hm2 => ?_⟩
        · have := ihP e' he'
          omega
        · rcases Nat.eq_or_lt_of_le hm1 with rfl | hm1
          · rw [h1]
            refine ⟨fun h' => absurd h' (by decide), fun ⟨e', he', h'⟩ => ?_⟩
            have := ihP e' he'
            omega
          · exact ih m' hm1 (by omega)

theorem testBit_low (k : Nat) : (2 ^ 135 - 1 : Nat).testBit k = decide (k < 135) :=
  Nat.testBit_two_pow_sub_one 135 k

theorem testBit_rowA (A i k : Nat) :
    (rowA A i).testBit k = (decide (k < 135) && A.testBit (135 * i + k)) := by
  unfold rowA
  change ((A >>> (135 * i)) &&& ((1 <<< 135) - 1)).testBit k = _
  rw [Nat.testBit_and, Nat.one_shiftLeft, testBit_low, Nat.testBit_shiftRight, Bool.and_comm]

theorem twB_iff (A m : Nat) : twB A m = true ↔ m / 135 ≠ m % 135 ∧ A.testBit m = false ∧
    ∀ l < 135, l ≠ m / 135 → l ≠ m % 135 →
      A.testBit (135 * (m / 135) + l) = A.testBit (135 * (m % 135) + l) := by
  unfold twB
  rw [strictB_eq, strictB_eq, bAnd_eq, bAnd_eq]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bitB_eq]
  have hd : (Nat.div m 135) = m / 135 := rfl
  have hmo : (Nat.mod m 135) = m % 135 := rfl
  rw [hd, hmo]
  set i := m / 135
  set j := m % 135
  have hz : ∀ X : Nat, Nat.beq X 0 = true ↔ ∀ k, X.testBit k = false := fun X => by
    rw [Nat.beq_eq]
    exact ⟨fun h k => by rw [h, Nat.zero_testBit], fun h => Nat.eq_of_testBit_eq fun k => by
      rw [h k, Nat.zero_testBit]⟩
  have hbit : ∀ k, (((rowA A i) ^^^ (rowA A j)) &&&
      (((1 <<< 135) - 1) ^^^ ((1 <<< i) ||| (1 <<< j)))).testBit k =
      (decide (k < 135) && (A.testBit (135 * i + k) ^^ A.testBit (135 * j + k)) &&
        !(decide (k = i) || decide (k = j))) := fun k => by
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_or, testBit_rowA,
      testBit_rowA, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft, testBit_low,
      Nat.testBit_two_pow, Nat.testBit_two_pow]
    by_cases hk : k < 135 <;> simp [hk, eq_comm]
  rw [hz]
  constructor
  · rintro ⟨hij, hm, hall⟩
    refine ⟨fun h => ?_, hm, fun l hl hli hlj => ?_⟩
    · rw [h, Nat.beq_refl] at hij
      cases hij
    · have := hall l
      change (((rowA A i) ^^^ (rowA A j)) &&&
        (((1 <<< 135) - 1) ^^^ ((1 <<< i) ||| (1 <<< j)))).testBit l = false at this
      rw [hbit] at this
      simp [hl, hli, hlj] at this
      exact this
  · rintro ⟨hij, hm, hall⟩
    refine ⟨?_, hm, fun k => ?_⟩
    · cases e : Nat.beq i j
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hij
    · change (((rowA A i) ^^^ (rowA A j)) &&&
        (((1 <<< 135) - 1) ^^^ ((1 <<< i) ||| (1 <<< j)))).testBit k = false
      rw [hbit]
      by_cases hk : k < 135
      · by_cases hki : k = i
        · simp [hki]
        · by_cases hkj : k = j
          · simp [hkj]
          · simp [hk, hki, hkj, hall k hk hki hkj]
      · simp [hk]

theorem low_eq (e : Nat) : Nat.land e (nat_lit 32767) = e % 32768 := by
  change e &&& 32767 = _
  rw [show (32767 : Nat) = 2 ^ 15 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem mid_eq (e : Nat) : Nat.land (Nat.shiftRight e (nat_lit 15)) (nat_lit 255) =
    e / 32768 % 256 := by
  change (e >>> 15) &&& 255 = _
  rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

theorem high_eq (e : Nat) : Nat.shiftRight e (nat_lit 23) = e / 2 ^ 23 := Nat.shiftRight_eq_div_pow e 23

theorem peK_spec {G : Nat → Nat} {F : List Nat} {e : Nat} (h : peK G F e = true) :
    e / 32768 % 256 < 135 ∧
      tA G (F.getD (e % 32768 / 135) 0) (F.getD (e % 32768 % 135) 0) = F.getD (e / 32768 % 256) 0 ∧
      F.getD (e / 32768 % 256) 0 ≠ F.getD (e % 32768 / 135) 0 ∧
      F.getD (e / 32768 % 256) 0 ≠ F.getD (e % 32768 % 135) 0 ∧
      e / 2 ^ 23 = tA G (F.getD (e % 32768 / 135) 0) (tA G (F.getD (e % 32768 % 135) 0) 0) := by
  unfold peK at h
  have hd : ∀ x : Nat, Nat.div x 135 = x / 135 := fun _ => rfl
  have hm : ∀ x : Nat, Nat.mod x 135 = x % 135 := fun _ => rfl
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Bool.not_eq_true', low_eq, mid_eq, high_eq,
    nthL_eq, hd, hm] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using h1, Nat.eq_of_beq_eq_true h2, fun e' => ?_, fun e' => ?_,
    Nat.eq_of_beq_eq_true h5⟩
  · change Nat.beq _ _ = false at h3
    rw [e', Nat.beq_refl] at h3
    cases h3
  · change Nat.beq _ _ = false at h4
    rw [e', Nat.beq_refl] at h4
    cases h4

theorem rotB_spec {p q : Nat} (h : rotB p q = true) :
    q % 32768 = p % 32768 ∨
      q % 32768 = 135 * (p % 32768 % 135) + p / 32768 % 256 ∨
      q % 32768 = 135 * (p / 32768 % 256) + p % 32768 / 135 := by
  unfold rotB at h
  simp only [strictB_eq, bIf_eq, low_eq, mid_eq] at h
  have hd : ∀ x : Nat, Nat.div x 135 = x / 135 := fun _ => rfl
  have hm : ∀ x : Nat, Nat.mod x 135 = x % 135 := fun _ => rfl
  simp only [hd, hm] at h
  split_ifs at h with h1 h2
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
  · exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h))

theorem keyK_spec {P : List Nat} (h : keyK P = true) : ∀ p ∈ P, ∀ q ∈ P,
    p / 2 ^ 23 = q / 2 ^ 23 → rotB p q = true := by
  have hi : ∀ (p : Nat) (Q : List Nat), List.rec (motive := fun _ => Bool) true
      (fun q _ ih' => bAnd(bIf(Nat.beq (Nat.shiftRight p (nat_lit 23))
        (Nat.shiftRight q (nat_lit 23)), rotB p q, true), ih')) Q = true →
      ∀ q ∈ Q, p / 2 ^ 23 = q / 2 ^ 23 → rotB p q = true := by
    intro p Q
    induction Q with
    | nil => exact fun _ q hq => absurd hq List.not_mem_nil
    | cons q Q ih =>
      intro hQ q' hq' hk
      change bAnd(bIf(Nat.beq (Nat.shiftRight p (nat_lit 23)) (Nat.shiftRight q (nat_lit 23)),
        rotB p q, true), _) = true at hQ
      rw [bAnd_eq, bIf_eq, Bool.and_eq_true] at hQ
      rcases List.mem_cons.1 hq' with rfl | hq'
      · rw [if_pos (by rw [high_eq, high_eq, hk]; exact Nat.beq_refl _)] at hQ
        exact hQ.1
      · exact ih hQ.2 q' hq' hk
  have ho : ∀ L : List Nat, List.rec (motive := fun _ => Bool) true (fun p _ ih => bAnd(
      List.rec (motive := fun _ => Bool) true (fun q _ ih' => bAnd(
        bIf(Nat.beq (Nat.shiftRight p (nat_lit 23)) (Nat.shiftRight q (nat_lit 23)), rotB p q,
          true), ih')) P, ih)) L = true → ∀ p ∈ L, List.rec (motive := fun _ => Bool) true
        (fun q _ ih' => bAnd(bIf(Nat.beq (Nat.shiftRight p (nat_lit 23))
          (Nat.shiftRight q (nat_lit 23)), rotB p q, true), ih')) P = true := by
    intro L
    induction L with
    | nil => exact fun _ p hp => absurd hp List.not_mem_nil
    | cons a L ih =>
      intro hL p hp
      dsimp only at hL
      rw [bAnd_eq, Bool.and_eq_true] at hL
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hL.1
      · exact ih hL.2 p hp
  intro p hp q hq hk
  exact hi p P (ho P h p hp) q hq hk

theorem bOr_eq (c d : Bool) : Bool.rec (motive := fun _ => Bool) d true c = (c || d) := by
  cases c <;> rfl

theorem pairIn_spec {T : List Nat} {a b : Nat} (h : pairIn T a b = true) :
    (a = T.getD 0 0 ∧ b = T.getD 1 0) ∨ (a = T.getD 1 0 ∧ b = T.getD 2 0) ∨
      (a = T.getD 2 0 ∧ b = T.getD 0 0) ∨ (a = T.getD 1 0 ∧ b = T.getD 0 0) ∨
        (a = T.getD 2 0 ∧ b = T.getD 1 0) ∨ (a = T.getD 0 0 ∧ b = T.getD 2 0) := by
  unfold pairIn at h
  simpa only [strictB_eq, bOr_eq, bAnd_eq, nthL_eq, Bool.or_eq_true, Bool.and_eq_true,
    Nat.beq_eq] using h

theorem inTr_spec {F : List Nat} {TR : List (List Nat)} {e : Nat} (h : inTr F TR e = true) :
    ∃ T ∈ TR, pairIn T (F.getD (e % 32768 / 135) 0) (F.getD (e % 32768 % 135) 0) = true := by
  unfold inTr at h
  simp only [strictB_eq, low_eq, nthL_eq] at h
  have hd : ∀ x : Nat, Nat.div x 135 = x / 135 := fun _ => rfl
  have hm : ∀ x : Nat, Nat.mod x 135 = x % 135 := fun _ => rfl
  simp only [hd, hm] at h
  induction TR with
  | nil => exact absurd h (by intro h'; cases h')
  | cons T TR ih =>
    dsimp only at h
    rw [bOr_eq, Bool.or_eq_true] at h
    rcases h with h1 | h
    · exact ⟨T, List.mem_cons_self, h1⟩
    · obtain ⟨T', hT', h2⟩ := ih h
      exact ⟨T', List.mem_cons_of_mem T hT', h2⟩

theorem trK_spec {G : Nat → Nat} {T : List Nat} (h : trK G T = true) :
    tA G (T.getD 0 0) (T.getD 1 0) = T.getD 2 0 ∧ tA G (T.getD 1 0) (T.getD 2 0) = T.getD 0 0 ∧
      tA G (T.getD 2 0) (T.getD 0 0) = T.getD 1 0 ∧ ∀ t < 6, tW G [T.getD 0 0, T.getD 1 0,
        T.getD 0 0, T.getD 1 0, T.getD 0 0, T.getD 1 0] t = t := by
  unfold trK at h
  simp only [strictB_eq, bAnd_eq, nthL_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    idK_spec h4⟩

theorem cmTr_spec {G : Nat → Nat} {T T' : List Nat} (h : cmTr G T T' = true) :
    (tA G (T'.getD 0 0) (tA G (T'.getD 1 0) (T.getD 0 0)) = T.getD 0 0 ∧
        tA G (T'.getD 0 0) (tA G (T'.getD 1 0) (T.getD 1 0)) = T.getD 1 0) ∨
      (tA G (T'.getD 0 0) (tA G (T'.getD 1 0) (T.getD 0 0)) = T.getD 1 0 ∧
        tA G (T'.getD 0 0) (tA G (T'.getD 1 0) (T.getD 1 0)) = T.getD 2 0) ∨
      (tA G (T'.getD 0 0) (tA G (T'.getD 1 0) (T.getD 0 0)) = T.getD 2 0 ∧
        tA G (T'.getD 0 0) (tA G (T'.getD 1 0) (T.getD 1 0)) = T.getD 0 0) := by
  unfold cmTr at h
  simpa only [strictB_eq, bOr_eq, bAnd_eq, nthL_eq, Bool.or_eq_true, Bool.and_eq_true,
    Nat.beq_eq] using h

theorem cmAll_spec {G : Nat → Nat} : ∀ {TR : List (List Nat)}, cmAll G TR = true →
    TR.Pairwise (fun T T' => cmTr G T T' = true)
  | [], _ => List.Pairwise.nil
  | T :: R, h => by
    have e : cmAll G (T :: R) = bAnd(List.rec (motive := fun _ => Bool) true
        (fun T' _ ih' => bAnd(cmTr G T T', ih')) R, cmAll G R) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    refine List.Pairwise.cons ?_ (cmAll_spec h.2)
    have hi : ∀ L : List (List Nat), List.rec (motive := fun _ => Bool) true
        (fun T' _ ih' => bAnd(cmTr G T T', ih')) L = true → ∀ T' ∈ L, cmTr G T T' = true := by
      intro L
      induction L with
      | nil => exact fun _ T' hT' => absurd hT' List.not_mem_nil
      | cons U L ih =>
        intro hL T' hT'
        dsimp only at hL
        rw [bAnd_eq, Bool.and_eq_true] at hL
        rcases List.mem_cons.1 hT' with rfl | hT'
        · exact hL.1
        · exact ih hL.2 T' hT'
    exact hi R h.1

theorem allLL_spec {f : List Nat → Bool} : ∀ {L : List (List Nat)}, allLL f L = true →
    ∀ x ∈ L, f x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | a :: L, h, x, hx => by
    have e : allLL f (a :: L) = bAnd(f a, allLL f L) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact allLL_spec h.2 x hx

theorem allL_spec {f : Nat → Bool} : ∀ {L : List Nat}, allL f L = true → ∀ x ∈ L, f x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | a :: L, h, x, hx => by
    have e : allL f (a :: L) = bAnd(f a, allL f L) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact allL_spec h.2 x hx

theorem tgK_spec {G : Nat → Nat} {w F g : List Nat} (h : tgK G w F g = true) :
    g.getD 0 0 < 31671 ∧ wv G w (g.getD 0 0) = g.getD 1 0 ∧ wv G w (g.getD 1 0) = g.getD 2 0 ∧
      ∀ a ∈ F, (g.getD 3 0).testBit a = cmK G a (g.getD 0 0) := by
  unfold tgK at h
  simp only [strictB_eq, bAnd_eq, nthL_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, ?_⟩
  clear h1 h2 h3
  induction F with
  | nil => exact fun a ha => absurd ha List.not_mem_nil
  | cons b F ih =>
    intro a ha
    dsimp only at h4
    rw [Bool.and_eq_true, bIf_eq] at h4
    rcases List.mem_cons.1 ha with rfl | ha
    · have h5 := h4.1
      rw [← bitB_eq]
      by_cases hc : cmK G a (g.getD 0 0) = true
      · rw [if_pos hc] at h5
        rw [h5, hc]
      · rw [if_neg hc, Bool.not_eq_true'] at h5
        rw [h5, Bool.eq_false_iff.2 hc]
    · exact ih h4.2 a ha

theorem fixAll_spec {G : Nat → Nat} {w : List Nat} : ∀ {ws : List Nat}, fixAll G w ws = true →
    ∀ a ∈ ws, a < 31671 ∧ wv G w a = a
  | [], _, a, ha => absurd ha List.not_mem_nil
  | b :: ws, h, a, ha => by
    have e : fixAll G w (b :: ws) =
        bAnd(Nat.blt b (nat_lit 31671), bAnd(Nat.beq (wv G w b) b, fixAll G w ws)) := rfl
    rw [e, bAnd_eq, bAnd_eq] at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨by simpa [Nat.blt_eq] using h.1, Nat.eq_of_beq_eq_true h.2.1⟩
    · exact fixAll_spec h.2.2 a ha

theorem cmV_cons (G : Nat → Nat) (r a : Nat) (ws : List Nat) :
    cmV G r (a :: ws) = if cmK G a r = true then 2 * cmV G r ws + 1 else 2 * cmV G r ws := by
  have e : cmV G r (a :: ws) = strictN (cmV G r ws) fun v =>
      nIf(cmK G a r, Nat.succ (Nat.mul (nat_lit 2) v), Nat.mul (nat_lit 2) v) := rfl
  rw [e, strictN_eq, nIf_eq]
  rfl

theorem sepB_spec {G : Nat → Nat} {r P : Nat} : ∀ {ws : List Nat},
    sepB P ws (cmV G r ws) = true → ∃ a ∈ ws, cmK G a r ≠ P.testBit a
  | [], h => absurd h (by intro h'; cases h')
  | a :: ws, h => by
    have e : sepB P (a :: ws) (cmV G r (a :: ws)) =
        bIf(bIf(bitB (cmV G r (a :: ws)) (nat_lit 0), Bool.not (bitB P a), bitB P a), true,
          sepB P ws (Nat.shiftRight (cmV G r (a :: ws)) (nat_lit 1))) := rfl
    have hb0 : bitB (cmV G r (a :: ws)) 0 = cmK G a r := by
      rw [bitB_eq, cmV_cons]
      split_ifs with hc
      · rw [hc, Nat.testBit_zero]
        simp
      · rw [Bool.eq_false_iff.2 hc, Nat.testBit_zero]
        simp
    have hsh : Nat.shiftRight (cmV G r (a :: ws)) 1 = cmV G r ws := by
      change cmV G r (a :: ws) >>> 1 = _
      rw [Nat.shiftRight_one, cmV_cons]
      split_ifs <;> omega
    rw [e, hb0, hsh, bIf_eq, bIf_eq, bitB_eq] at h
    by_cases h1 : (if cmK G a r = true then !P.testBit a else P.testBit a) = true
    · refine ⟨a, List.mem_cons_self, fun h2 => ?_⟩
      rw [h2] at h1
      cases P.testBit a <;> simp at h1
    · rw [if_neg h1] at h
      obtain ⟨b, hb, h2⟩ := sepB_spec h
      exact ⟨b, List.mem_cons_of_mem a hb, h2⟩

theorem repK_spec {G : Nat → Nat} {w : List Nat} {TG : List (List Nat)} {e : List Nat}
    (h : repK G w TG e = true) : e ≠ [] ∧ e.getD 0 0 < 31671 ∧
      (∀ a ∈ e.tail, a < 31671 ∧ wv G w a = a) ∧ ∀ g ∈ TG,
        e.getD 0 0 = g.getD 0 0 ∨ e.getD 0 0 = g.getD 1 0 ∨ e.getD 0 0 = g.getD 2 0 ∨
          ∃ a ∈ e.tail, cmK G a (e.getD 0 0) ≠ (g.getD 3 0).testBit a := by
  cases e with
  | nil => exact absurd h (by intro h'; cases h')
  | cons r ws =>
    have e1 : repK G w TG (r :: ws) = bAnd(Nat.blt r (nat_lit 31671), bAnd(fixAll G w ws,
        strictB (cmV G r ws) fun V => List.rec (motive := fun _ => Bool) true
          (fun g _ ih => bAnd(tg1 g r ws V, ih)) TG)) := rfl
    rw [e1, bAnd_eq, bAnd_eq, strictB_eq] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨List.cons_ne_nil r ws, by simpa [Nat.blt_eq] using h1, fixAll_spec h2, ?_⟩
    clear h1 h2 e1
    simp only [List.getD_cons_zero, List.tail_cons]
    induction TG with
    | nil => exact fun g hg => absurd hg List.not_mem_nil
    | cons g TG ih =>
      intro g' hg'
      dsimp only at h3
      rw [bAnd_eq, Bool.and_eq_true] at h3
      rcases List.mem_cons.1 hg' with rfl | hg'
      · have h4 := h3.1
        unfold tg1 at h4
        simp only [bOr_eq, nthL_eq, Bool.or_eq_true, Nat.beq_eq] at h4
        rcases h4 with k1 | k2 | k3 | k4
        · exact Or.inl k1
        · exact Or.inr (Or.inl k2)
        · exact Or.inr (Or.inr (Or.inl k3))
        · exact Or.inr (Or.inr (Or.inr (sepB_spec k4)))
      · exact ih h3.2 g' hg'

theorem repAll_spec {G : Nat → Nat} {w : List Nat} {TG : List (List Nat)} :
    ∀ {R : List (List Nat)}, repAll G w TG R = true → ∀ e ∈ R, repK G w TG e = true
  | [], _, e, he => absurd he List.not_mem_nil
  | a :: R, h, e, he => by
    have e1 : repAll G w TG (a :: R) = bAnd(repK G w TG a, repAll G w TG R) := rfl
    rw [e1, bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact repAll_spec h.2 e he

theorem covU_testBit {G : Nat → Nat} {w : List Nat} (c : Nat) : ∀ (R : List (List Nat)) (acc : Nat),
    (covU G w R acc).testBit c = true → acc.testBit c = true ∨ ∃ e ∈ R,
      c = e.getD 0 0 ∨ c = wv G w (e.getD 0 0) ∨ c = wv G w (wv G w (e.getD 0 0))
  | [], acc, h => Or.inl h
  | e :: R, acc, h => by
    have e1 : covU G w (e :: R) acc =
        strictN (Nat.lor acc (orbBits G w (nthL e (nat_lit 0)))) (covU G w R) := rfl
    rw [e1, strictN_eq] at h
    rcases covU_testBit c R _ h with h1 | ⟨e', he', h2⟩
    · change (acc ||| orbBits G w (nthL e 0)).testBit c = true at h1
      rw [Nat.testBit_or, Bool.or_eq_true] at h1
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr ⟨e, List.mem_cons_self, ?_⟩
        unfold orbBits at h1
        rw [strictN_eq, strictN_eq, nthL_eq] at h1
        change ((1 <<< _ ||| 1 <<< _) ||| 1 <<< _).testBit c = true at h1
        simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
          decide_eq_true_eq] at h1
        rcases h1 with (h1 | h1) | h1
        · exact Or.inl h1.symm
        · exact Or.inr (Or.inl h1.symm)
        · exact Or.inr (Or.inr h1.symm)
    · exact Or.inr ⟨e', List.mem_cons_of_mem e he', h2⟩

end CFSG.KC.Fi23Tw

end
