module

public import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commute.Defs

public section

open scoped commutatorElement

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem mul_eq_commutator_mul_mul {x y : G} : y * x = ⁅y, x⁆ * x * y := by
  rw [commutatorElement_def]
  group

theorem mul_pow_three_of_commute {x y : G} (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) :
    (x * y) ^ 3 = ⁅y, x⁆ ^ 3 * x ^ 3 * y ^ 3 := by
  set c := ⁅y, x⁆ with hc
  have hyx : y * x = c * x * y := mul_eq_commutator_mul_mul
  have hxc : x * c = c * x := hx.eq.symm
  have hyc : y * c = c * y := hy.eq.symm
  have hxc2 : x * c ^ 2 = c ^ 2 * x := ((hx.symm).pow_right 2).eq
  have hxxc2 : x * (x * c ^ 2) = c ^ 2 * x * x := by rw [hxc2, ← mul_assoc, hxc2]
  have hy2x : y ^ 2 * x = c ^ 2 * x * y ^ 2 := by
    calc y ^ 2 * x = y * (y * x) := by simp only [pow_two, mul_assoc]
      _ = y * (c * x * y) := by rw [hyx]
      _ = (y * c) * x * y := by simp only [mul_assoc]
      _ = (c * y) * x * y := by rw [hyc]
      _ = c * (y * x) * y := by simp only [mul_assoc]
      _ = c * (c * x * y) * y := by rw [hyx]
      _ = c ^ 2 * x * y ^ 2 := by simp only [pow_two, mul_assoc]
  calc (x * y) ^ 3 = x * (y * x) * y * x * y := by simp only [pow_three, mul_assoc]
    _ = x * (c * x * y) * y * x * y := by rw [hyx]
    _ = x * c * x * (y ^ 2 * x) * y := by simp only [pow_two, mul_assoc]
    _ = x * c * x * (c ^ 2 * x * y ^ 2) * y := by rw [hy2x]
    _ = c * x * x * (c ^ 2 * x * y ^ 2) * y := by rw [hxc]
    _ = c * (x * (x * c ^ 2)) * x * y ^ 2 * y := by simp only [mul_assoc]
    _ = c * (c ^ 2 * x * x) * x * y ^ 2 * y := by rw [hxxc2]
    _ = c ^ 3 * x ^ 3 * y ^ 3 := by simp only [pow_two, pow_three, mul_assoc]

theorem commutatorElement_mul_right_of_commute {x a b : G} (h : Commute ⁅x, b⁆ a) :
    ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
  have hd : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
    rw [← h.eq, mul_inv_cancel_right]
  calc ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, a⁆ * ⁅x, b⁆ := by rw [hd]

theorem commutatorElement_pow_three_of_commute {x a : G} (h : Commute ⁅x, a⁆ a) :
    ⁅x, a ^ 3⁆ = ⁅x, a⁆ ^ 3 :=
  (h.symm.commutatorElement_pow_right 3).symm

theorem commutatorElement_mul_left_of_commute_reversed {x a b : G} (h : Commute ⁅b, x⁆ a) :
    ⁅a * b, x⁆ = ⁅b, x⁆ * ⁅a, x⁆ := by
  have hd : a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ := by
    rw [← h.eq, mul_inv_cancel_right]
  calc ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅b, x⁆ * ⁅a, x⁆ := by rw [hd]

end CFSG.GroupTheory.HuppertProduct
