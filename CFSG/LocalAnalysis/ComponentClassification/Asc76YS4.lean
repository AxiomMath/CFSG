module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup

variable {X : Type*} [Group X]

theorem braid_of_orderOf_le_three {X : Type*} [Group X] [Finite X] {x y : X} (hx : x * x = 1)
    (hy : y * y = 1) (h3 : orderOf (x * y) ≤ 3) (hne : x * y ≠ y * x) : x * y * x = y * x * y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hpos := orderOf_pos (x * y)
  interval_cases hk : orderOf (x * y)
  · exfalso
    apply hne
    have h1 : x * y = 1 := orderOf_eq_one_iff.1 hk
    rw [show y = x⁻¹ from eq_inv_of_mul_eq_one_right h1, hxi]
  · exfalso
    apply hne
    have h2 : (x * y) ^ 2 = 1 := by rw [← hk, pow_orderOf_eq_one]
    rw [sq] at h2
    have := eq_inv_of_mul_eq_one_left h2
    rw [this, mul_inv_rev, hxi, hyi]
  · have h3' : (x * y) ^ 3 = 1 := by rw [← hk, pow_orderOf_eq_one]
    have e : x * y * x * (y * x * y) = 1 := by
      rw [show x * y * x * (y * x * y) = x * y * (x * y * (x * y)) by simp only [mul_assoc],
        ← pow_three, h3']
    rw [eq_inv_of_mul_eq_one_left e, mul_inv_rev, mul_inv_rev, hxi, hyi, mul_assoc]

end CFSG.ComponentClassification.Asc76.Sec4
