module

public import Mathlib.Analysis.Complex.ExponentialBounds

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Real

theorem one_add_inv_pow_succ_lt {q n : ℕ} (hq : 4 ≤ q) (hn : q ≤ n) :
    (1 + (n : ℝ)⁻¹) ^ (q + 1) < q := by
  have hn4 : 4 ≤ n := hq.trans hn
  have hn4' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hx1 : (1 : ℝ) ≤ 1 + (n : ℝ)⁻¹ := by
    have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    linarith
  have hxle : 1 + (n : ℝ)⁻¹ ≤ 5 / 4 := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 4 by norm_num) hn4'
    rw [one_div (n : ℝ)] at h
    linarith
  calc (1 + (n : ℝ)⁻¹) ^ (q + 1) ≤ (1 + (n : ℝ)⁻¹) ^ (n + 1) :=
        pow_le_pow_right₀ hx1 (by omega)
    _ = (1 + (n : ℝ)⁻¹) ^ n * (1 + (n : ℝ)⁻¹) := by rw [pow_succ]
    _ ≤ rexp 1 * (5 / 4) :=
        mul_le_mul Real.one_add_inv_pow_le_exp hxle (by linarith) (exp_nonneg 1)
    _ < 4 := by nlinarith [Real.exp_one_lt_d9]
    _ ≤ q := by exact_mod_cast hq

theorem succ_pow_lt_mul_pow {q n : ℕ} (hq : 4 ≤ q) (hn : q ≤ n) :
    (n + 1) ^ (q + 1) < q * n ^ (q + 1) := by
  have hn4 : 4 ≤ n := hq.trans hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    linarith
  rw [← Nat.cast_lt (α := ℝ)]
  push_cast
  have key := one_add_inv_pow_succ_lt hq hn
  have h1 : ((n : ℝ) + 1) = n * (1 + (n : ℝ)⁻¹) := by field_simp
  rw [h1, mul_pow]
  have hpos : (0 : ℝ) < (n : ℝ) ^ (q + 1) := by positivity
  calc (n : ℝ) ^ (q + 1) * (1 + (n : ℝ)⁻¹) ^ (q + 1) < (n : ℝ) ^ (q + 1) * q :=
        mul_lt_mul_of_pos_left key hpos
    _ = q * (n : ℝ) ^ (q + 1) := by ring

theorem pow_succ_lt_pow_succ_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    ∀ n, q + 1 ≤ n → n ^ (q + 1) < q ^ (n + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      calc (q + 1) ^ (q + 1) < q * q ^ (q + 1) := succ_pow_lt_mul_pow hq le_rfl
        _ = q ^ (q + 1 + 1) := by ring
  | succ n hn ih =>
      calc (n + 1) ^ (q + 1) < q * n ^ (q + 1) := succ_pow_lt_mul_pow hq (by omega)
        _ ≤ q * q ^ (n + 1) := Nat.mul_le_mul le_rfl ih.le
        _ = q ^ (n + 1 + 1) := by ring

theorem pow_four_lt_three_pow_succ : ∀ n, 5 ≤ n → n ^ 4 < 3 ^ (n + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have a : 5 * n ≤ n ^ 2 := by nlinarith
      have b : 5 * n ^ 2 ≤ n ^ 3 := by nlinarith
      have c : 5 * n ^ 3 ≤ n ^ 4 := by nlinarith
      calc (n + 1) ^ 4 < 3 * n ^ 4 := by nlinarith
        _ < 3 * 3 ^ (n + 1) := by gcongr
        _ = 3 ^ (n + 1 + 1) := by ring

theorem pow_succ_lt_pow_succ_of_odd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hlt : q < p) : p ^ (q + 1) < q ^ (p + 1) := by
  rw [Nat.odd_iff] at hpodd hqodd
  have hq2 := hq.two_le
  have hp2 := hp.two_le
  rcases (show q = 3 ∨ 5 ≤ q by omega) with rfl | hq5
  · exact pow_four_lt_three_pow_succ p (by omega)
  · exact pow_succ_lt_pow_succ_of_four_le (by omega) p (by omega)

end CFSG.FeitThompson
