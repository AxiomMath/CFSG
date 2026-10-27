module

public import CFSG.LargeExtraspecial.O62SL4

public section

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup
open scoped MatrixGroups

theorem false_of_orderOf_eq_nine {K : Type*} [Group K] {H : Subgroup K} (hH : H.index = 2)
    (e : H ≃* SL(4, ZMod 2)) (x : K) (hx : orderOf x = 9) : False := by
  set y : H := ⟨x ^ 2, Subgroup.sq_mem_of_index_two hH x⟩
  have hy : orderOf y = 9 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (x ^ 2) = 9
    rw [orderOf_pow' x (by norm_num : (2 : ℕ) ≠ 0), hx]
    norm_num
  have hey : orderOf (e y) = 9 := by rw [MulEquiv.orderOf_eq]; exact hy
  have h9 : (e y) ^ 9 = 1 := by rw [← hey]; exact pow_orderOf_eq_one _
  have h3 := O62.SL4.pow_three_eq_one_of_pow_nine (e y) h9
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hey] at this
  norm_num at this

theorem exists_orderOf_eq_nine_of_dvd {K : Type*} [Group K] {x : K} (h0 : orderOf x ≠ 0)
    (h9 : 9 ∣ orderOf x) : ∃ y : K, orderOf y = 9 := by
  obtain ⟨m, hm⟩ := h9
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact h0 (by rw [hm, mul_zero])
  refine ⟨x ^ m, ?_⟩
  rw [orderOf_pow' x hm0, hm, Nat.gcd_mul_left_left]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)

end CFSG.LargeExtraspecial.S14.W4Loc
