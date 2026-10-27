module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

@[expose] def splitCount (q : ℚ) (r k : ℕ) : ℚ :=
  (∏ j ∈ Finset.range k, ((q ^ (r - j) - 1) * (q ^ (r - j - 1) + 1))) /
    ∏ i ∈ Finset.Icc 1 k, (q ^ i - 1)

@[expose] def splitMaxIndex (q : ℚ) (r : ℕ) : ℚ :=
  ∏ i ∈ Finset.Icc 1 (r - 1), (q ^ i + 1)

@[expose] def qNum (q : ℚ) (r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range r, q ^ i

theorem min_le_of_ratio_anti {a R : ℕ → ℚ} {m n : ℕ} (ha : ∀ i, m ≤ i → i ≤ n → 0 < a i)
    (hR : ∀ i, a (i + 1) = a i * R i) (hdec : ∀ i j, m ≤ i → i < j → j < n → R j < R i)
    {k : ℕ} (hmk : m ≤ k) (hkn : k ≤ n) : min (a m) (a n) ≤ a k := by
  by_contra hlt
  rw [not_le] at hlt
  have hdesc : ∃ i, m ≤ i ∧ i < k ∧ a (i + 1) < a i := by
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    have hmono : ∀ l, m ≤ l → l ≤ k → a m ≤ a l := by
      intro l hml hlk
      induction l, hml using Nat.le_induction with
      | base => exact le_rfl
      | succ l hml ih => exact (ih (by omega)).trans (h l hml (by omega))
    exact absurd (hmono k hmk le_rfl) (not_le.mpr (lt_of_lt_of_le hlt (min_le_left _ _)))
  have hasc : ∃ j, k ≤ j ∧ j < n ∧ a j < a (j + 1) := by
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    have hanti : ∀ l, k ≤ l → l ≤ n → a l ≤ a k := by
      intro l hkl hln
      induction l, hkl using Nat.le_induction with
      | base => exact le_rfl
      | succ l hkl ih => exact (h l hkl (by omega)).trans (ih (by omega))
    exact absurd (hanti n hkn le_rfl) (not_le.mpr (lt_of_lt_of_le hlt (min_le_right _ _)))
  obtain ⟨i, hmi, hik, hi⟩ := hdesc
  obtain ⟨j, hkj, hjn, hj⟩ := hasc
  have hai := ha i hmi (by omega)
  have haj := ha j (by omega) (by omega)
  rw [hR] at hi hj
  have hRi : R i < 1 := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hRj : 1 < R j := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have := hdec i j hmi (by omega) hjn
  linarith

theorem prod_Icc_one_range {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∏ i ∈ Finset.Icc 1 k, f i = ∏ j ∈ Finset.range k, f (j + 1) := by
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' f 0 k 1, zero_add,
    Finset.Ico_add_one_right_eq_Icc]

section Arith

variable {q : ℚ}

theorem splitCount_succ (r k : ℕ) : splitCount q r (k + 1) =
    splitCount q r k * ((q ^ (r - k) - 1) * (q ^ (r - k - 1) + 1) / (q ^ (k + 1) - 1)) := by
  rw [splitCount, splitCount, Finset.prod_range_succ,
    Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
  exact mul_div_mul_comm _ _ _ _

theorem qNum_mul_sub_one (r : ℕ) : qNum q r * (q - 1) = q ^ r - 1 := by
  rw [qNum, geom_sum_mul]

variable (hq : 2 ≤ q)
include hq

theorem pow_sub_one_pos_of_two_le {m : ℕ} (hm : 1 ≤ m) : 0 < q ^ m - 1 := by
  have := one_lt_pow₀ (by linarith : 1 < q) (by omega : m ≠ 0)
  linarith

theorem pow_add_one_pos_of_two_le (m : ℕ) : 0 < q ^ m + 1 := by
  have : 0 ≤ q ^ m := pow_nonneg (by linarith) m
  linarith

theorem splitCount_pos {r k : ℕ} (hk : k ≤ r) : 0 < splitCount q r k := by
  refine div_pos (Finset.prod_pos fun j hj => mul_pos ?_ (pow_add_one_pos_of_two_le hq _))
    (Finset.prod_pos fun i hi => pow_sub_one_pos_of_two_le hq (Finset.mem_Icc.mp hi).1)
  rw [Finset.mem_range] at hj
  exact pow_sub_one_pos_of_two_le hq (by omega)

theorem splitMaxIndex_pos (r : ℕ) : 0 < splitMaxIndex q r :=
  Finset.prod_pos fun i _ => pow_add_one_pos_of_two_le hq i

theorem qNum_pos {r : ℕ} (hr : 1 ≤ r) : 0 < qNum q r := by
  have h := qNum_mul_sub_one (q := q) r
  have h1 := pow_sub_one_pos_of_two_le hq hr
  have h2 : 0 < q - 1 := by linarith
  by_contra hle
  rw [not_lt] at hle
  nlinarith

theorem splitCount_one (r : ℕ) : splitCount q r 1 = qNum q r * (q ^ (r - 1) + 1) := by
  have hq1 : q - 1 ≠ 0 := by linarith
  rw [splitCount, Finset.prod_range_one, Finset.Icc_self, Finset.prod_singleton, pow_one,
    Nat.sub_zero, ← qNum_mul_sub_one r]
  field_simp

theorem splitCount_pred {r : ℕ} (hr : 1 ≤ r) :
    splitCount q r (r - 1) = qNum q r * splitMaxIndex q r := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hN : (∏ j ∈ Finset.range m, (q ^ (m + 1 - j) - 1)) * (q - 1) =
      (∏ i ∈ Finset.Icc 1 m, (q ^ i - 1)) * (q ^ (m + 1) - 1) := by
    rw [← Finset.prod_range_reflect (fun j => q ^ (m + 1 - j) - 1) m, prod_Icc_one_range]
    have e1 : ∀ j ∈ Finset.range m, q ^ (m + 1 - (m - 1 - j)) - 1 = q ^ (j + 1 + 1) - 1 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show m + 1 - (m - 1 - j) = j + 1 + 1 by omega]
    rw [Finset.prod_congr rfl e1]
    have h := Finset.prod_range_succ' (fun j => q ^ (j + 1) - 1) m
    have h' := Finset.prod_range_succ (fun j => q ^ (j + 1) - 1) m
    simp only [zero_add, pow_one] at h h'
    rw [← h, h']
  have hP : ∏ j ∈ Finset.range m, (q ^ (m + 1 - j - 1) + 1) =
      ∏ i ∈ Finset.Icc 1 m, (q ^ i + 1) := by
    rw [← Finset.prod_range_reflect (fun j => q ^ (m + 1 - j - 1) + 1) m, prod_Icc_one_range]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show m + 1 - (m - 1 - j) - 1 = j + 1 by omega]
  have hD : ∏ i ∈ Finset.Icc 1 m, (q ^ i - 1) ≠ 0 :=
    (Finset.prod_pos fun i hi => pow_sub_one_pos_of_two_le hq (Finset.mem_Icc.mp hi).1).ne'
  have hq1 : q - 1 ≠ 0 := by linarith
  have hqn : qNum q (m + 1) = (q ^ (m + 1) - 1) / (q - 1) := by
    rw [eq_div_iff hq1, qNum_mul_sub_one]
  have hND : (∏ j ∈ Finset.range m, (q ^ (m + 1 - j) - 1)) /
      (∏ i ∈ Finset.Icc 1 m, (q ^ i - 1)) = (q ^ (m + 1) - 1) / (q - 1) := by
    rw [div_eq_div_iff hD hq1]
    linear_combination hN
  rw [splitCount, Finset.prod_mul_distrib, hP, splitMaxIndex, Nat.add_sub_cancel, hqn,
    mul_div_right_comm, hND]

omit hq in
theorem splitMaxIndex_eq_mul {r : ℕ} (hr : 2 ≤ r) :
    splitMaxIndex q r = (∏ i ∈ Finset.Icc 1 (r - 2), (q ^ i + 1)) * (q ^ (r - 1) + 1) := by
  rw [splitMaxIndex, show r - 1 = r - 2 + 1 by omega,
    Finset.prod_Icc_succ_top (by omega : 1 ≤ r - 2 + 1)]

theorem qNum_lt_prod_pow_add_one {m : ℕ} (hm : 3 ≤ m) :
    qNum q (m + 2) < ∏ i ∈ Finset.Icc 1 m, (q ^ i + 1) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have : Finset.Icc 1 3 = {1, 2, 3} := by decide
    rw [this, qNum, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    nlinarith [pow_pos (by linarith : (0 : ℚ) < q) 3, pow_pos (by linarith : (0 : ℚ) < q) 5,
      pow_pos (by linarith : (0 : ℚ) < q) 6]
  | succ m hm ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), qNum, Finset.sum_range_succ, ← qNum]
    have hge : 1 + q ≤ qNum q (m + 2) := by
      rw [qNum, Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ', pow_zero, pow_one]
      have : 0 ≤ ∑ i ∈ Finset.range m, q ^ (i + 1 + 1) :=
        Finset.sum_nonneg fun i _ => pow_nonneg (by linarith) _
      linarith
    have hpow : 0 < q ^ (m + 1) := pow_pos (by linarith) _
    have hpos : 0 < ∏ i ∈ Finset.Icc 1 m, (q ^ i + 1) :=
      Finset.prod_pos fun i _ => pow_add_one_pos_of_two_le hq i
    rw [show m + 1 + 1 = m + 2 by omega, pow_succ]
    nlinarith

end Arith

theorem orthogonal_geometry_split_count_comparison {q r : ℕ} (hq : 2 ≤ q) (hr : 3 ≤ r) :
    (∀ k, k ≤ r → 0 < splitCount q r k) ∧ 0 < splitMaxIndex q r ∧
      splitCount q r 1 = qNum q r * ((q : ℚ) ^ (r - 1) + 1) ∧
      (∀ k, 2 ≤ k → k ≤ r - 1 → splitCount q r 1 < splitCount q r k) ∧
      splitMaxIndex q 4 = splitCount q 4 1 ∧
      (5 ≤ r → splitCount q r 1 < splitMaxIndex q r ∧
        ∀ k, 2 ≤ k → k ≤ r - 1 → splitCount q r 1 < splitCount q r k) := by
  have hQ : (2 : ℚ) ≤ q := by exact_mod_cast hq
  set Q : ℚ := (q : ℚ) with hQdef
  have hmain : ∀ k, 2 ≤ k → k ≤ r - 1 → splitCount Q r 1 < splitCount Q r k := by
    intro k hk2 hkr
    set R : ℕ → ℚ := fun i => (Q ^ (r - i) - 1) * (Q ^ (r - i - 1) + 1) / (Q ^ (i + 1) - 1)
      with hRdef
    have hrec : ∀ i, splitCount Q r (i + 1) = splitCount Q r i * R i := fun i =>
      splitCount_succ r i
    have hdec : ∀ i j, 2 ≤ i → i < j → j < r - 1 → R j < R i := by
      intro i j hi hij hjr
      have hQ1 : 1 < Q := by linarith
      have hn1 : Q ^ (r - j) < Q ^ (r - i) := pow_lt_pow_right₀ hQ1 (by omega)
      have hn2 : Q ^ (r - j - 1) < Q ^ (r - i - 1) := pow_lt_pow_right₀ hQ1 (by omega)
      have hd : Q ^ (i + 1) < Q ^ (j + 1) := pow_lt_pow_right₀ hQ1 (by omega)
      have hp1 := pow_sub_one_pos_of_two_le hQ (m := r - j) (by omega)
      have hp2 := pow_add_one_pos_of_two_le hQ (r - j - 1)
      have hp3 := pow_sub_one_pos_of_two_le hQ (m := i + 1) (by omega)
      have hNj : 0 < (Q ^ (r - j) - 1) * (Q ^ (r - j - 1) + 1) := mul_pos hp1 hp2
      have hNlt : (Q ^ (r - j) - 1) * (Q ^ (r - j - 1) + 1) <
          (Q ^ (r - i) - 1) * (Q ^ (r - i - 1) + 1) := by nlinarith
      simp only [hRdef]
      rw [div_lt_div_iff₀ (by linarith) hp3]
      nlinarith
    have hmin := min_le_of_ratio_anti (a := fun i => splitCount Q r i) (R := R) (m := 2)
      (n := r - 1) (fun i _ hi => splitCount_pos hQ (by omega)) hrec hdec hk2 hkr
    have h12 : splitCount Q r 1 < splitCount Q r 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, hrec 1]
      have hpos := splitCount_pos hQ (r := r) (k := 1) (by omega)
      have hR1 : 1 < R 1 := by
        simp only [hRdef]
        have hp := pow_sub_one_pos_of_two_le hQ (m := 1 + 1) (by omega)
        rw [lt_div_iff₀ hp, one_mul]
        have h1 : Q ^ (1 + 1) ≤ Q ^ (r - 1) := pow_le_pow_right₀ (by linarith) (by omega)
        have h2 : 0 < Q ^ (r - 1 - 1) := pow_pos (by linarith) _
        nlinarith
      nlinarith
    have h1n : splitCount Q r 1 < splitCount Q r (r - 1) := by
      rw [splitCount_pred hQ (by omega), splitCount_one hQ, splitMaxIndex_eq_mul (by omega)]
      have hqn := qNum_pos hQ (r := r) (by omega)
      have hgt : 1 < ∏ i ∈ Finset.Icc 1 (r - 2), (Q ^ i + 1) := by
        rw [show r - 2 = r - 3 + 1 by omega, Finset.prod_Icc_succ_top (by omega)]
        have h1 : 1 ≤ ∏ i ∈ Finset.Icc 1 (r - 3), (Q ^ i + 1) :=
          Finset.one_le_prod₀ fun i _ => by
            have : 0 ≤ Q ^ i := pow_nonneg (by linarith) i
            linarith
        have h2 : 1 < Q ^ (r - 3 + 1) + 1 := by
          have : 0 < Q ^ (r - 3 + 1) := pow_pos (by linarith) _
          linarith
        nlinarith
      have hp := pow_add_one_pos_of_two_le hQ (r - 1)
      exact mul_lt_mul_of_pos_left (lt_mul_left hp hgt) hqn
    have := lt_min h12 h1n
    exact lt_of_lt_of_le this hmin
  have hA : 5 ≤ r → splitCount Q r 1 < splitMaxIndex Q r := by
    intro hr5
    rw [splitCount_one hQ, splitMaxIndex_eq_mul (by omega)]
    have h := qNum_lt_prod_pow_add_one hQ (m := r - 2) (by omega)
    rw [show r - 2 + 2 = r by omega] at h
    have hp := pow_add_one_pos_of_two_le hQ (r - 1)
    nlinarith
  refine ⟨fun k hk => splitCount_pos hQ hk, splitMaxIndex_pos hQ r, splitCount_one hQ r,
    hmain, ?_, fun hr5 => ⟨hA hr5, hmain⟩⟩
  rw [splitCount_one hQ, splitMaxIndex]
  have : Finset.Icc 1 (4 - 1) = {1, 2, 3} := by decide
  rw [this, qNum, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
