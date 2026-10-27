module

public import Mathlib.Algebra.Group.Basic

public section

namespace CFSG

theorem commute_of_sq_eq_one {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hy)
  have hxy' : x * y * (x * y) = 1 := by rw [← pow_two]; exact hxy
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy').symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

end CFSG

end
