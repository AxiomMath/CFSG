module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem four_mul_le_three_mul_sub_one_sq {e : ℝ} (he : 3 ≤ e) :
    4 * e ≤ 3 * (e - 1) ^ 2 := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e - 3) (by linarith : (0 : ℝ) ≤ 3 * e - 1)]

theorem index_lt_four_of_norm_bounds
    {k b m h e : ℕ} (hk : 0 < k) (hb : 0 < b) (hm : 0 < m) (hh : 0 < h)
    (_hbk : b ≤ k) (he : 3 ≤ e) (hmkh : m ≤ k * h)
    {u v : ℝ}
    (hu : ((k : ℝ) - b) / m * ((e : ℝ) - 1) ^ 2 ≤ u)
    (hv : 1 - (e : ℝ) / h ≤ v)
    (huv : u + v < 1) :
    (k : ℝ) / b < 4 := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have hH : (0 : ℝ) < h := by exact_mod_cast hh
  have hE : (3 : ℝ) ≤ e := by exact_mod_cast he
  have hMKH : (m : ℝ) ≤ (k : ℝ) * h := by
    have : ((m : ℕ) : ℝ) ≤ ((k * h : ℕ) : ℝ) := by exact_mod_cast hmkh
    push_cast at this
    exact this
  have hS : (0 : ℝ) < ((e : ℝ) - 1) ^ 2 := by
    have : (0 : ℝ) < (e : ℝ) - 1 := by linarith
    positivity
  have key : ((k : ℝ) - b) / m * ((e : ℝ) - 1) ^ 2 < (e : ℝ) / h := by linarith
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ hM hH] at key
  have hem : (e : ℝ) * m ≤ (e : ℝ) * k * h := by
    have := mul_le_mul_of_nonneg_left hMKH (by linarith : (0 : ℝ) ≤ (e : ℝ))
    linarith [this]
  have hstep : ((k : ℝ) - b) * ((e : ℝ) - 1) ^ 2 < (e : ℝ) * k := by
    have h1 : (((k : ℝ) - b) * ((e : ℝ) - 1) ^ 2) * h < ((e : ℝ) * k) * h := by
      calc (((k : ℝ) - b) * ((e : ℝ) - 1) ^ 2) * h < (e : ℝ) * m := key
        _ ≤ ((e : ℝ) * k) * h := hem
    exact lt_of_mul_lt_mul_right h1 hH.le
  have h34 : 4 * (e : ℝ) ≤ 3 * ((e : ℝ) - 1) ^ 2 := four_mul_le_three_mul_sub_one_sq hE
  have hk4b : (k : ℝ) < 4 * b := by
    rcases lt_or_ge ((k : ℝ)) (4 * b) with h | h
    · exact h
    · exact absurd hstep (by nlinarith [mul_nonneg hS.le (by linarith : (0 : ℝ) ≤ (k : ℝ) - 4 * b),
        mul_le_mul_of_nonneg_right h34 hK.le])
  rw [div_lt_iff₀ hB]
  linarith

theorem lt_four_mul_of_norm_bounds
    {k b m h e : ℕ} (hk : 0 < k) (hb : 0 < b) (hm : 0 < m) (hh : 0 < h)
    (hbk : b ≤ k) (he : 3 ≤ e) (hmkh : m ≤ k * h)
    {u v : ℝ}
    (hu : ((k : ℝ) - b) / m * ((e : ℝ) - 1) ^ 2 ≤ u)
    (hv : 1 - (e : ℝ) / h ≤ v)
    (huv : u + v < 1) :
    k < 4 * b := by
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  have := index_lt_four_of_norm_bounds hk hb hm hh hbk he hmkh hu hv huv
  rw [div_lt_iff₀ hB] at this
  have : (k : ℝ) < ((4 * b : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

end CFSG.FeitThompson
