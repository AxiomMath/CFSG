module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Finset

@[expose] def isoTerm (q m : ℕ) : ℚ := (q : ℚ) ^ m - (-1) ^ m

@[expose] def isoIndexCount (q n k : ℕ) : ℚ :=
  (∏ j ∈ range k, ((q : ℚ) ^ (n - 2 * j) - (-1) ^ (n - 2 * j)) *
      ((q : ℚ) ^ (n - 2 * j - 1) - (-1) ^ (n - 2 * j - 1))) /
    ∏ i ∈ Icc 1 k, ((q : ℚ) ^ (2 * i) - 1)

theorem prod_Icc_eq_prod_range (q k : ℕ) :
    ∏ i ∈ Icc 1 k, ((q : ℚ) ^ (2 * i) - 1) = ∏ i ∈ range k, ((q : ℚ) ^ (2 * i + 2) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_Icc_succ_top (by omega), ih, prod_range_succ]
    congr 2

theorem numerator_eq (q m k : ℕ) :
    ∏ j ∈ range k, ((q : ℚ) ^ (m + 2 * k - 2 * j) - (-1) ^ (m + 2 * k - 2 * j)) *
      ((q : ℚ) ^ (m + 2 * k - 2 * j - 1) - (-1) ^ (m + 2 * k - 2 * j - 1)) =
    ∏ i ∈ range k, isoTerm q (m + 2 * i + 1) * isoTerm q (m + 2 * i + 2) := by
  conv_rhs => rw [← prod_range_reflect]
  refine prod_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [isoTerm, isoTerm, mul_comm, show m + 2 * (k - 1 - j) + 1 = m + 2 * k - 2 * j - 1 by omega,
    show m + 2 * (k - 1 - j) + 2 = m + 2 * k - 2 * j by omega]

theorem isoIndexCount_shift (q m k : ℕ) :
    isoIndexCount q (m + 2 * k) k =
      (∏ i ∈ range k, isoTerm q (m + 2 * i + 1) * isoTerm q (m + 2 * i + 2)) /
        ∏ i ∈ range k, ((q : ℚ) ^ (2 * i + 2) - 1) := by
  rw [isoIndexCount, numerator_eq, prod_Icc_eq_prod_range]

theorem isoIndexCount_one (q n : ℕ) :
    isoIndexCount q n 1 = isoTerm q (n - 1) * isoTerm q n / ((q : ℚ) ^ 2 - 1) := by
  rw [isoIndexCount, prod_range_one, Icc_self, prod_singleton]
  simp only [mul_zero, Nat.sub_zero, mul_one]
  rw [isoTerm, isoTerm, mul_comm]

theorem isoIndexCount_succ (q m l : ℕ) :
    isoIndexCount q (m + 2 * (l + 1)) (l + 1) = isoIndexCount q (m + 2 * (l + 1)) 1 *
      ∏ i ∈ range l, isoTerm q (m + 2 * i + 1) * isoTerm q (m + 2 * i + 2) /
        ((q : ℚ) ^ (2 * i + 4) - 1) := by
  have h4 : ∀ i : ℕ, (q : ℚ) ^ (2 * (i + 1) + 2) - 1 = (q : ℚ) ^ (2 * i + 4) - 1 := fun i => by
    rw [show 2 * (i + 1) + 2 = 2 * i + 4 by ring]
  rw [isoIndexCount_shift, isoIndexCount_one,
    prod_range_succ (fun i => isoTerm q (m + 2 * i + 1) * isoTerm q (m + 2 * i + 2)) l,
    prod_range_succ' (fun i => (q : ℚ) ^ (2 * i + 2) - 1) l, prod_div_distrib,
    show m + 2 * (l + 1) - 1 = m + 2 * l + 1 by omega,
    show m + 2 * (l + 1) = m + 2 * l + 2 by ring]
  simp only [h4]
  rw [div_mul_div_comm]
  congr 1 <;> ring

theorem isoTerm_even (q i : ℕ) : isoTerm q (2 * i) = (q : ℚ) ^ (2 * i) - 1 := by
  rw [isoTerm, (even_two_mul i).neg_one_pow]

theorem isoTerm_odd (q i : ℕ) : isoTerm q (2 * i + 1) = (q : ℚ) ^ (2 * i + 1) + 1 := by
  rw [isoTerm, (odd_two_mul_add_one i).neg_one_pow, sub_neg_eq_add]

theorem isoTerm_ge (q m : ℕ) : (q : ℚ) ^ m - 1 ≤ isoTerm q m := by
  rw [isoTerm]
  rcases neg_one_pow_eq_or ℚ m with h | h <;> linarith

theorem isoTerm_le (q m : ℕ) : isoTerm q m ≤ (q : ℚ) ^ m + 1 := by
  rw [isoTerm]
  rcases neg_one_pow_eq_or ℚ m with h | h <;> linarith

theorem two_le_pow {q m : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) : (2 : ℚ) ≤ (q : ℚ) ^ m := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  exact le_trans hq' (by simpa using pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ q) hm)

theorem pow_sub_one_pos {q m : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) : 0 < (q : ℚ) ^ m - 1 := by
  linarith [two_le_pow hq hm]

theorem isoTerm_pos {q m : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) : 0 < isoTerm q m := by
  linarith [isoTerm_ge q m, two_le_pow hq hm]

theorem isoTerm_mono {q a b : ℕ} (hq : 2 ≤ q) (ha : 1 ≤ a) (hab : a ≤ b) :
    isoTerm q a ≤ isoTerm q b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℚ) ^ (a + 1) ≤ (q : ℚ) ^ b := pow_le_pow_right₀ (by linarith) hab
  have h2 := two_le_pow hq ha
  have h3 : (q : ℚ) ^ (a + 1) = q * q ^ a := by ring
  nlinarith [isoTerm_le q a, isoTerm_ge q b]

theorem lt_isoTerm_mul_even (q i : ℕ) (hq : 2 ≤ q) :
    (q : ℚ) ^ (2 * i + 4) - 1 < isoTerm q (2 * i + 2) * isoTerm q (2 * i + 3) := by
  rw [show 2 * i + 2 = 2 * (i + 1) by ring, show 2 * i + 3 = 2 * (i + 1) + 1 by ring,
    isoTerm_even, isoTerm_odd]
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  set x : ℚ := (q : ℚ) ^ (2 * (i + 1)) with hx
  have hx2 : (q : ℚ) ^ 2 ≤ x := pow_le_pow_right₀ (by linarith) (by omega)
  have e1 : (q : ℚ) ^ (2 * (i + 1) + 1) = q * x := by rw [hx]; ring
  have e2 : (q : ℚ) ^ (2 * i + 4) = q ^ 2 * x := by rw [hx]; ring
  rw [e1, e2]
  have hxpos : 0 < x := by nlinarith
  have hc : 0 < q * x + 1 - q - q ^ 2 := by nlinarith
  nlinarith [mul_pos hxpos hc]

theorem lt_isoTerm_mul_odd (q i : ℕ) (hq : 2 ≤ q) (hi : 1 ≤ i) :
    (q : ℚ) ^ (2 * i + 4) - 1 < isoTerm q (2 * i + 1) * isoTerm q (2 * i + 2) := by
  rw [show 2 * i + 2 = 2 * (i + 1) by ring, isoTerm_even, isoTerm_odd]
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  set y : ℚ := (q : ℚ) ^ (2 * i + 1) with hy
  have hy3 : (q : ℚ) ^ 3 ≤ y := pow_le_pow_right₀ (by linarith) (by omega)
  have e1 : (q : ℚ) ^ (2 * (i + 1)) = q * y := by rw [hy]; ring
  have e2 : (q : ℚ) ^ (2 * i + 4) = q ^ 3 * y := by rw [hy]; ring
  rw [e1, e2]
  have hq3 : (0 : ℚ) < (q : ℚ) ^ 3 := by positivity
  have hypos : 0 < y := by linarith
  have hc : 0 < q * y - 1 + q - q ^ 3 := by nlinarith
  nlinarith [mul_pos hypos hc]

theorem lt_isoTerm_first_two (q : ℕ) (hq : 2 ≤ q) :
    ((q : ℚ) ^ 4 - 1) * ((q : ℚ) ^ 6 - 1) <
      isoTerm q 1 * isoTerm q 2 * (isoTerm q 3 * isoTerm q 4) := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have h1 : isoTerm q 1 = q + 1 := by norm_num [isoTerm]
  have h2 : isoTerm q 2 = q ^ 2 - 1 := by norm_num [isoTerm]
  have h3 : isoTerm q 3 = q ^ 3 + 1 := by norm_num [isoTerm]
  have h4 : isoTerm q 4 = q ^ 4 - 1 := by norm_num [isoTerm]
  rw [h1, h2, h3, h4]
  have hpos : 0 < ((q : ℚ) ^ 4 - 1) * ((q : ℚ) ^ 4 + q) * (q - 1) :=
    mul_pos (mul_pos (pow_sub_one_pos hq (by norm_num)) (by positivity)) (by linarith)
  nlinarith [hpos]

theorem isoIndexCount_one_pos {q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) : 0 < isoIndexCount q n 1 := by
  rw [isoIndexCount_one]
  exact div_pos (mul_pos (isoTerm_pos hq (by omega)) (isoTerm_pos hq (by omega)))
    (pow_sub_one_pos hq (by norm_num))

theorem isoIndexCount_pos {q n k : ℕ} (hq : 2 ≤ q) (hk : 2 * k ≤ n) : 0 < isoIndexCount q n k := by
  refine div_pos (prod_pos fun j hj => ?_) (prod_pos fun i hi => ?_)
  · rw [mem_range] at hj
    exact mul_pos (isoTerm_pos hq (by omega)) (isoTerm_pos hq (by omega))
  · rw [mem_Icc] at hi
    exact pow_sub_one_pos hq (by omega)

theorem isoIndexCount_one_lt {q n k : ℕ} (hq : 2 ≤ q) (hn : 5 ≤ n) (hk2 : 2 ≤ k)
    (hk : k ≤ n / 2) : isoIndexCount q n 1 < isoIndexCount q n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * k := ⟨n - 2 * k, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  rw [isoIndexCount_succ]
  refine lt_mul_of_one_lt_right (isoIndexCount_one_pos hq (by omega)) ?_
  have hD : ∀ i : ℕ, 0 < (q : ℚ) ^ (2 * i + 4) - 1 := fun i => pow_sub_one_pos hq (by omega)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  ·
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
    rw [prod_range_succ', prod_range_succ']
    simp only [zero_add, mul_zero, mul_one]
    have hlater : 1 ≤ ∏ i ∈ range l, isoTerm q (2 * (i + 1 + 1) + 1) *
        isoTerm q (2 * (i + 1 + 1) + 2) / ((q : ℚ) ^ (2 * (i + 1 + 1) + 4) - 1) :=
      one_le_prod₀ fun i _ => by
        rw [le_div_iff₀ (hD _), one_mul]
        exact (lt_isoTerm_mul_odd q _ hq (by omega)).le
    have hfirst : 1 < isoTerm q (2 * 1 + 1) * isoTerm q (2 * 1 + 2) / ((q : ℚ) ^ (2 * 1 + 4) - 1) *
        (isoTerm q 1 * isoTerm q 2 / ((q : ℚ) ^ 4 - 1)) := by
      rw [div_mul_div_comm, one_lt_div (mul_pos (hD 1) (hD 0))]
      have := lt_isoTerm_first_two q hq
      norm_num at this ⊢
      linarith
    calc (1 : ℚ) < 1 * (isoTerm q (2 * 1 + 1) * isoTerm q (2 * 1 + 2) /
          ((q : ℚ) ^ (2 * 1 + 4) - 1) * (isoTerm q 1 * isoTerm q 2 / ((q : ℚ) ^ 4 - 1))) := by
          rw [one_mul]
          exact hfirst
      _ ≤ _ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hlater (by linarith)
  ·
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have hfac : ∀ i : ℕ, 1 < isoTerm q (m + 2 * i + 1) * isoTerm q (m + 2 * i + 2) /
        ((q : ℚ) ^ (2 * i + 4) - 1) := fun i => by
      rw [one_lt_div (hD i)]
      have h1 := isoTerm_mono hq (a := 2 * i + 2) (b := m + 2 * i + 1) (by omega) (by omega)
      have h2 := isoTerm_mono hq (a := 2 * i + 3) (b := m + 2 * i + 2) (by omega) (by omega)
      have h3 := lt_isoTerm_mul_even q i hq
      have h4 := isoTerm_pos hq (m := 2 * i + 2) (by omega)
      have h5 := isoTerm_pos hq (m := 2 * i + 3) (by omega)
      nlinarith [mul_le_mul h1 h2 h5.le (h4.le.trans h1)]
    rw [prod_range_succ]
    calc (1 : ℚ) < 1 * (isoTerm q (m + 2 * l + 1) * isoTerm q (m + 2 * l + 2) /
          ((q : ℚ) ^ (2 * l + 4) - 1)) := by
          rw [one_mul]
          exact hfac l
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_prod₀ fun i _ => (hfac i).le)
          (by linarith [hfac l])

theorem isoIndexCount_four_one {q : ℕ} (hq : 2 ≤ q) :
    isoIndexCount q 4 1 = ((q : ℚ) ^ 2 + 1) * ((q : ℚ) ^ 3 + 1) := by
  have h2 := pow_sub_one_pos hq (m := 2) (by norm_num)
  rw [isoIndexCount_one, div_eq_iff h2.ne']
  norm_num [isoTerm]
  ring

theorem isoIndexCount_four_two {q : ℕ} (hq : 2 ≤ q) :
    isoIndexCount q 4 2 = ((q : ℚ) + 1) * ((q : ℚ) ^ 3 + 1) := by
  have h2 := pow_sub_one_pos hq (m := 2) (by norm_num)
  have h4 := pow_sub_one_pos hq (m := 4) (by norm_num)
  rw [show (4 : ℕ) = 0 + 2 * 2 from rfl, isoIndexCount_shift,
    div_eq_iff (prod_pos fun i _ => pow_sub_one_pos hq (by omega)).ne']
  norm_num [isoTerm, prod_range_succ]
  ring

theorem isotropic_index_comparison {q n : ℕ} (hq : 2 ≤ q) :
    (∀ k ≤ n / 2, 0 < isoIndexCount q n k) ∧
    (5 ≤ n → ∀ k, 2 ≤ k → k ≤ n / 2 → isoIndexCount q n 1 < isoIndexCount q n k) ∧
    (n = 4 → isoIndexCount q 4 1 = ((q : ℚ) ^ 2 + 1) * ((q : ℚ) ^ 3 + 1) ∧
      isoIndexCount q 4 2 = ((q : ℚ) + 1) * ((q : ℚ) ^ 3 + 1) ∧
      isoIndexCount q 4 2 < isoIndexCount q 4 1) ∧
    (n = 2 ∨ n = 3 → ∀ k, 1 ≤ k → k ≤ n / 2 → k = 1) := by
  refine ⟨fun k hk => isoIndexCount_pos hq (by omega),
    fun hn5 k hk2 hk => isoIndexCount_one_lt hq hn5 hk2 hk, fun _ => ?_, fun h k hk1 hk => ?_⟩
  · refine ⟨isoIndexCount_four_one hq, isoIndexCount_four_two hq, ?_⟩
    rw [isoIndexCount_four_one hq, isoIndexCount_four_two hq]
    have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
    have h3 : (0 : ℚ) < (q : ℚ) ^ 3 + 1 := by positivity
    exact mul_lt_mul_of_pos_right (by nlinarith) h3
  · omega

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
