module

import Mathlib.Tactic.FieldSimp
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem three_mul_sq_lt_three_pow {p : ℕ} (hp : 5 ≤ p) : 3 * p ^ 2 < 3 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h : (n + 1) ^ 2 < 3 * n ^ 2 := by nlinarith
    have hpow : (3 : ℕ) ^ (n + 1) = 3 * 3 ^ n := by ring
    rw [hpow]
    nlinarith [ih, h]

theorem sq_lt_three_pow_sub_one {p : ℕ} (hp : 5 ≤ p) : p ^ 2 < 3 ^ (p - 1) := by
  have h := three_mul_sq_lt_three_pow hp
  have h3 : (3 : ℕ) ^ p = 3 * 3 ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem sq_sub_one_div_six_lt_ratio_mul_sq_div_three {p : ℕ} (hp : 5 ≤ p) :
    ((p : ℝ) ^ 2 - 1) / 6 < (1 - (3 : ℝ) ^ (1 - (p : ℤ))) / 2 * (p : ℝ) ^ 2 / 3 := by
  have h3 : (0 : ℝ) < 3 ^ p := by positivity
  have key : 3 * (p : ℝ) ^ 2 < 3 ^ p := by
    have := three_mul_sq_lt_three_pow hp
    exact_mod_cast this
  have hexp : (3 : ℝ) ^ (1 - (p : ℤ)) = 3 / 3 ^ p := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, zpow_natCast]
  have hlt : 3 * (p : ℝ) ^ 2 / 3 ^ p < 1 := by
    rw [div_lt_one h3]; exact key
  have hrw : (1 - 3 / (3 : ℝ) ^ p) / 2 * (p : ℝ) ^ 2 / 3
      = ((p : ℝ) ^ 2 - 3 * (p : ℝ) ^ 2 / 3 ^ p) / 6 := by
    field_simp
    ring
  rw [hexp, hrw]
  linarith

theorem sq_sub_one_div_six_lt_of_ratio_mul_sq_div_three_lt {p : ℕ} (hp : 5 ≤ p) {u : ℝ}
    (hu : (1 - (3 : ℝ) ^ (1 - (p : ℤ))) / 2 * (p : ℝ) ^ 2 / 3 < u) :
    ((p : ℝ) ^ 2 - 1) / 6 < u :=
  (sq_sub_one_div_six_lt_ratio_mul_sq_div_three hp).trans hu

end CFSG.FeitThompson
