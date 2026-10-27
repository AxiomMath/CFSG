module

import Mathlib.Tactic.FieldSimp
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem inv_two_mul_le_one_sub_sub_inv
    {e p u b : ℝ} (he : 3 ≤ e) (hp : 0 < p) (hu : 7 ≤ u)
    (hb : b ≤ 1 / (u * p) + (e - 1) * (p - 1) / (e * p)) :
    1 / (2 * p) ≤ 1 - b - 1 / e := by
  have he0 : (0:ℝ) < e := by linarith
  have hu0 : (0:ℝ) < u := by linarith
  have hb' : b * (e * p * u) ≤ e + u * ((e - 1) * (p - 1)) := by
    have h1 : 1 / (u * p) * (e * p * u) = e := by field_simp
    have h2 : (e - 1) * (p - 1) / (e * p) * (e * p * u) = u * ((e - 1) * (p - 1)) := by
      field_simp
    calc b * (e * p * u) ≤ (1 / (u * p) + (e - 1) * (p - 1) / (e * p)) * (e * p * u) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = e + u * ((e - 1) * (p - 1)) := by rw [add_mul, h1, h2]
  have hx : e * (1 / e) = 1 := by field_simp
  have key : u * e - e - u ≤ (1 - b - 1 / e) * (e * p * u) := by
    nlinarith [hb', hx, mul_pos hp hu0]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * p)]
  nlinarith [key, mul_nonneg (sub_nonneg.2 he) (sub_nonneg.2 hu)]

theorem div_lt_inv_two_mul {e p h : ℝ} (he : 0 < e) (hp : 0 < p)
    (hh : p * (2 * e + 1) ≤ h) : e / h < 1 / (2 * p) := by
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hh
  rw [div_lt_div_iff₀ hh0 (by positivity : (0:ℝ) < 2 * p)]
  nlinarith [hh, mul_pos hp he]

theorem not_exists_packet_bound_and_lt_div
    {e p u h : ℝ} (he : 3 ≤ e) (hp : 0 < p) (hu : 7 ≤ u) (hh : p * (2 * e + 1) ≤ h) :
    ¬ ∃ b : ℝ, b ≤ 1 / (u * p) + (e - 1) * (p - 1) / (e * p) ∧ 1 - b - 1 / e < e / h := by
  rintro ⟨b, hb1, hb2⟩
  have h1 := inv_two_mul_le_one_sub_sub_inv he hp hu hb1
  have h2 := div_lt_inv_two_mul (e := e) (p := p) (h := h) (by linarith) hp hh
  linarith

end CFSG.FeitThompson
