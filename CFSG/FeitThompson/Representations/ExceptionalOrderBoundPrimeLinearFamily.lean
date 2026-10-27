module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Int.Defs
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

namespace ExceptionalOrderBound

section

variable {p m : ℤ} (hp : Odd p) (hp0 : 0 < p) (hm : Odd m) (hm3 : 3 ≤ m)
  (hdvd : m ∣ p + 1) (hle : p ^ 2 ≤ 4 * m ^ 2 + 1)

include hp hp0 hm hm3 hdvd hle

theorem eq_two_mul_sub_one : p = 2 * m - 1 := by
  have hm0 : (0 : ℤ) < m := by omega
  obtain ⟨k, hk⟩ := hdvd
  have hkeven : Even k := by
    have hev : Even (m * k) := by rw [← hk]; exact hp.add_one
    rcases Int.even_mul.mp hev with h | h
    · exact absurd h (Int.not_even_iff_odd.mpr hm)
    · exact h
  obtain ⟨t, ht⟩ := hkeven
  have hpt : p + 1 = 2 * m * t := by rw [hk, ht]; ring
  have ht1 : 1 ≤ t := by
    rcases le_or_gt 1 t with h | h
    · exact h
    · exact absurd hpt (by nlinarith [mul_nonneg hm0.le (neg_nonneg.mpr (by omega : t ≤ 0))])
  have ht' : t = 1 := by
    by_contra hne
    have hp4 : 4 * m - 1 ≤ p := by
      nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr (by omega : (2 : ℤ) ≤ t))]
    nlinarith
  rw [ht'] at hpt
  linarith

theorem divisor_lt : m < p := by
  have := eq_two_mul_sub_one hp hp0 hm hm3 hdvd hle
  omega

theorem sq_sub_one_eq : p ^ 2 - 1 = 4 * (m - 1) * m := by
  have h := eq_two_mul_sub_one hp hp0 hm hm3 hdvd hle
  subst h; ring

theorem sq_sub_one_ediv_eq : (p ^ 2 - 1) / m = 4 * (m - 1) := by
  rw [sq_sub_one_eq hp hp0 hm hm3 hdvd hle, Int.mul_ediv_cancel _ (by omega : m ≠ 0)]

theorem eight_le_sq_sub_one_ediv : 8 ≤ (p ^ 2 - 1) / m := by
  rw [sq_sub_one_ediv_eq hp hp0 hm hm3 hdvd hle]; omega

theorem eq_neg_one_and_eq_two {δ n : ℤ} (hδ : δ = 1 ∨ δ = -1) (hn : 1 ≤ n)
    (hpn : p - δ = n * m) : δ = -1 ∧ n = 2 := by
  have hpm := eq_two_mul_sub_one hp hp0 hm hm3 hdvd hle
  rcases hδ with rfl | rfl
  ·
    refine absurd hpn ?_
    rw [hpm]
    rcases le_or_gt n 1 with h | h
    · intro hc; nlinarith
    · intro hc; nlinarith
  · refine ⟨rfl, mul_right_cancel₀ (by omega : m ≠ 0) ?_⟩
    rw [hpm] at hpn
    linarith

end

end ExceptionalOrderBound

end CFSG.FeitThompson
