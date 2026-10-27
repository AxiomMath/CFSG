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

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Sp

theorem two_mul_sum_Icc_two {n : ℕ} (hn : 1 ≤ n) :
    2 * ∑ i ∈ Finset.Icc 2 n, i + 2 = n * (n + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have h := ih hpos
      nlinarith [h]

theorem prod_Icc_pow_sub_one_le (q n : ℕ) :
    ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) ≤ q ^ (∑ i ∈ Finset.Icc 2 n, i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun i _ => Nat.sub_le _ _

theorem sum_Icc_one_two_mul (m : ℕ) : ∑ i ∈ Finset.Icc 1 m, 2 * i = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem prod_Icc_pow_two_mul_sub_one_le (q m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ q ^ (m * (m + 1)) := by
  have h1 : ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ ∏ i ∈ Finset.Icc 1 m, q ^ (2 * i) :=
    Finset.prod_le_prod fun i _ => Nat.sub_le _ _
  rw [Finset.prod_pow_eq_pow_sum, sum_Icc_one_two_mul] at h1
  exact h1

theorem four_mul_prod_Icc_pow_add_one_mul_le {q n : ℕ} (hq : 3 ≤ q) (hn : 2 ≤ n) :
    (4 : ℤ) * (∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i + 1)) * (q : ℤ) ^ n ≤
      5 * (q : ℤ) ^ (∑ i ∈ Finset.Icc 2 n, i) * ((q : ℤ) ^ n - 1) := by
  have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.prod_singleton, Finset.sum_singleton]
    have h9 : (0 : ℤ) ≤ (q : ℤ) ^ 2 - 9 := by nlinarith
    nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ 2) h9]
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    set P := ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i + 1)
    set S := ∑ i ∈ Finset.Icc 2 n, i
    have hx : (0 : ℤ) < (q : ℤ) ^ n := by positivity
    have key : ((q : ℤ) ^ n - 1) * ((q : ℤ) ^ (n + 1) + 1) * q ≤
        (q : ℤ) ^ (n + 1) * ((q : ℤ) ^ (n + 1) - 1) := by
      rw [pow_succ]
      nlinarith [mul_pos hx (by linarith : (0 : ℤ) < (q : ℤ) - 2)]
    calc (4 : ℤ) * (P * ((q : ℤ) ^ (n + 1) + 1)) * (q : ℤ) ^ (n + 1) =
        (4 * P * (q : ℤ) ^ n) * (((q : ℤ) ^ (n + 1) + 1) * q) := by ring
      _ ≤ (5 * (q : ℤ) ^ S * ((q : ℤ) ^ n - 1)) * (((q : ℤ) ^ (n + 1) + 1) * q) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ = 5 * (q : ℤ) ^ S * (((q : ℤ) ^ n - 1) * ((q : ℤ) ^ (n + 1) + 1) * q) := by ring
      _ ≤ 5 * (q : ℤ) ^ S * ((q : ℤ) ^ (n + 1) * ((q : ℤ) ^ (n + 1) - 1)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = 5 * (q : ℤ) ^ (S + (n + 1)) * ((q : ℤ) ^ (n + 1) - 1) := by ring

theorem four_mul_prod_Icc_pow_add_one_le {q n : ℕ} (hq : 3 ≤ q) (hn : 2 ≤ n) :
    4 * ∏ i ∈ Finset.Icc 2 n, (q ^ i + 1) ≤ 5 * q ^ (∑ i ∈ Finset.Icc 2 n, i) := by
  have h := four_mul_prod_Icc_pow_add_one_mul_le hq hn
  have hx : (0 : ℤ) < (q : ℤ) ^ n := by positivity
  have h' : (4 : ℤ) * (∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i + 1)) ≤
      5 * (q : ℤ) ^ (∑ i ∈ Finset.Icc 2 n, i) := by
    by_contra hc
    push Not at hc
    have h3 := mul_lt_mul_of_pos_right hc hx
    nlinarith [(by positivity : (0 : ℤ) < 5 * (q : ℤ) ^ (∑ i ∈ Finset.Icc 2 n, i))]
  exact_mod_cast h'

theorem psp4_sq_lower {q : ℕ} (hq : 3 ≤ q) :
    3 * q ^ 12 ≤ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) ^ 2 := by
  have e2 : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
    push_cast [Nat.one_le_iff_ne_zero.2 (by positivity : q ^ 2 ≠ 0)]
    ring
  have e4 : ((q ^ 4 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 4 - 1 := by
    push_cast [Nat.one_le_iff_ne_zero.2 (by positivity : q ^ 4 ≠ 0)]
    ring
  have key : (3 : ℤ) * (q : ℤ) ^ 12 ≤ 4 * (((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 - 1)) ^ 2 := by
    have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
    have h2' : (9 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((q : ℤ) ^ 2), sq_nonneg ((q : ℤ) ^ 4), sq_nonneg ((q : ℤ) ^ 6),
      mul_pos (by positivity : (0 : ℤ) < (q : ℤ) ^ 4) (by nlinarith : (0 : ℤ) < (q : ℤ) ^ 2 - 1)]
  have : ((3 * q ^ 12 : ℕ) : ℤ) ≤ ((4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) ^ 2 : ℕ) : ℤ) := by
    push_cast [e2, e4]
    exact key
  exact_mod_cast this

end CFSG.ComponentClassification.CatLeafProof.X10Sp
