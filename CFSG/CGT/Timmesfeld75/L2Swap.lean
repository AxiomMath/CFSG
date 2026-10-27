module

public import CFSG.CGT.Timmesfeld75.L2Defs

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem pow_three_eq_one_of_trace_eq_one {g : SL(2, F)} (h : g 0 0 + g 1 1 = 1) : g ^ 3 = 1 := by
  have hD := sl2_det g
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [pow_three]
  apply sl2_ext
  all_goals sl2_simp
  · linear_combination (g 0 0 * (g 0 0 + g 1 1 + 1) - 1) * h - (2 * g 0 0 + g 1 1) * hD - h2
  · linear_combination (g 0 1 * (g 0 0 + g 1 1 + 1)) * h - g 0 1 * hD
  · linear_combination (g 1 0 * (g 0 0 + g 1 1 + 1)) * h - g 1 0 * hD
  · linear_combination (g 1 1 * (g 0 0 + g 1 1 + 1) - 1) * h - (g 0 0 + 2 * g 1 1) * hD - h2

theorem orderOf_eq_three_of_trace_eq_one {g : SL(2, F)} (h : g 0 0 + g 1 1 = 1) (hg : g ≠ 1) :
    orderOf g = 3 :=
  orderOf_eq_prime (pow_three_eq_one_of_trace_eq_one h) hg

theorem orderOf_utriElt_inv_mul_of_mul_self_eq_one {t : SL(2, F)} (htt : t * t = 1)
    (hc : t 1 0 ≠ 0) : orderOf (utriElt (t 1 0)⁻¹ * t) = 3 := by
  have h10 := congrArg (fun x : SL(2, F) => x 1 0) htt
  simp only [mul_apply_10, one_apply_10] at h10
  have hsum : t 0 0 + t 1 1 = 0 := by
    have h1 : t 1 0 * (t 0 0 + t 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.1 h1).resolve_left hc
  have hs : (t 1 0)⁻¹ * t 1 0 = 1 := inv_mul_cancel₀ hc
  have htr : (utriElt (t 1 0)⁻¹ * t) 0 0 + (utriElt (t 1 0)⁻¹ * t) 1 1 = 1 := by
    simp only [mul_apply_00, mul_apply_11, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11]
    linear_combination hsum + hs
  refine orderOf_eq_three_of_trace_eq_one htr fun h1 => hc ?_
  have h2 := congrArg (fun x : SL(2, F) => x 1 0) h1
  simp only [mul_apply_10, utriElt_apply_10, utriElt_apply_11, one_apply_10] at h2
  linear_combination h2

end Matrix

end CFSG.CGT.Timmesfeld75
