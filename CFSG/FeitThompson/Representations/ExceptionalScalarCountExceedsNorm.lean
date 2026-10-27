module

import Mathlib.Tactic.FieldSimp
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem cubic_bound_lt_two_mul_add_one_pow {a : ℝ} (ha : 1 ≤ a) {q : ℕ} (hq : 3 ≤ q) :
    ((q : ℝ) + 2) * a ^ 3 + (q : ℝ) ^ 2 * a ^ 2 + 2 * q * a + 1 < (2 * a + 1) ^ q := by
  induction q, hq using Nat.le_induction with
  | base => push_cast; nlinarith [sq_nonneg a, sq_nonneg (a - 1)]
  | succ q hq ih =>
    have hQ : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hpos : (0 : ℝ) < 2 * a + 1 := by linarith
    have h2 := mul_lt_mul_of_pos_left ih hpos
    have ha2 : (0 : ℝ) ≤ a ^ 2 := by positivity
    have ha3 : (0 : ℝ) ≤ a ^ 3 := by positivity
    have ha4 : (0 : ℝ) ≤ a ^ 4 := by positivity
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by linarith
    have hsq : (0 : ℝ) ≤ (q : ℝ) ^ 2 - 9 := by nlinarith
    push_cast
    rw [show (2 * a + 1) ^ (q + 1) = (2 * a + 1) * (2 * a + 1) ^ q by ring]
    nlinarith [h2, mul_nonneg hq0 ha4, mul_nonneg hsq ha3, mul_nonneg hq0 ha2]

theorem lt_of_exceptional_count_eq {a q u p : ℕ} (ha : 1 ≤ a) (hq : 3 ≤ q) (hu : 1 ≤ u)
    (hua : u ≤ a ^ 2) (hp : p = 2 * a + 1) {N : ℝ}
    (hN : (q : ℝ) * u * N + ((p : ℝ) - 1) * ((q : ℝ) + u) = (p : ℝ) ^ q - 1) :
    (a : ℝ) + 1 + ((q : ℝ) - 1) * (a : ℝ) ^ 2 / u < N := by
  have hA : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hQ : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hU : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hU0 : (u : ℝ) ≠ 0 := by positivity
  have hUA : (u : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast hua
  have hpos : (0 : ℝ) < (q : ℝ) * u := by nlinarith
  have hbin := cubic_bound_lt_two_mul_add_one_pow hA hq
  have hpR : (p : ℝ) = 2 * (a : ℝ) + 1 := by rw [hp]; push_cast; ring
  rw [hpR] at hN
  have key : (q : ℝ) * u * ((a : ℝ) + 1) + (q : ℝ) * ((q : ℝ) - 1) * (a : ℝ) ^ 2
      < (q : ℝ) * u * N := by
    nlinarith [hbin, mul_nonneg (sub_nonneg.2 hUA) (by linarith : (0:ℝ) ≤ (q:ℝ)),
      mul_nonneg (sub_nonneg.2 hUA) (by positivity : (0:ℝ) ≤ (a:ℝ)),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hUA) (by linarith : (0:ℝ) ≤ (q:ℝ)))
        (by linarith : (0:ℝ) ≤ (a:ℝ) + 1)]
  refine lt_of_mul_lt_mul_left ?_ hpos.le
  calc (q : ℝ) * u * ((a : ℝ) + 1 + ((q : ℝ) - 1) * (a : ℝ) ^ 2 / u)
      = (q : ℝ) * u * ((a : ℝ) + 1) + (q : ℝ) * ((q : ℝ) - 1) * (a : ℝ) ^ 2 := by
        field_simp
    _ < (q : ℝ) * u * N := key

theorem pos_of_exceptional_count_eq {a q u p : ℕ} (ha : 1 ≤ a) (hq : 3 ≤ q) (hu : 1 ≤ u)
    (hua : u ≤ a ^ 2) (hp : p = 2 * a + 1) {N : ℝ}
    (hN : (q : ℝ) * u * N + ((p : ℝ) - 1) * ((q : ℝ) + u) = (p : ℝ) ^ q - 1) :
    0 < N := by
  have h := lt_of_exceptional_count_eq ha hq hu hua hp hN
  have hA : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hQ : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hU : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hnn : (0 : ℝ) ≤ ((q : ℝ) - 1) * (a : ℝ) ^ 2 / u :=
    div_nonneg (by nlinarith [sq_nonneg ((a : ℝ))]) (by linarith)
  linarith

end CFSG.FeitThompson
