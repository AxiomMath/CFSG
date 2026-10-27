module

public import CFSG.FeitThompson.OddOrder.ConjugateComplementsReordering
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem conj_mul_inv_eq_of_conj_mul_conj_eq_sq {Q : Subgroup G} [IsMulCommutative Q]
    {s y t A B : G} (hsQ : s ∈ Subgroup.normalizer Q) (hy : y ∈ Q) (ht : t = y⁻¹ * s * y)
    (hAB : (A⁻¹ * s * A) * (B⁻¹ * s * B) = s ^ 2) :
    s ^ 3 * ((t ^ 2)⁻¹ * (A * B⁻¹) * t ^ 2) * s⁻¹
      = t * (s * ((t ^ 3)⁻¹ * A⁻¹ * t ^ 3) * (s ^ 2)⁻¹)⁻¹ * (t ^ 2)⁻¹
        * (s ^ 2 * (t⁻¹ * B * t) * (s ^ 3)⁻¹)⁻¹ * t := by
  have hAB' : A * B⁻¹ = s⁻¹ * A * s ^ 2 * B⁻¹ * s⁻¹ := by rw [← hAB]; group
  have h12 : t⁻¹ * (s ^ 2)⁻¹ * t = (t ^ 2)⁻¹ * s⁻¹ * t ^ 2 * s⁻¹ := by
    simpa using conj_inv_pow_reorder hsQ hy ht (i := 1) (j := 2) (by decide)
  have h13 : t⁻¹ * (s ^ 3)⁻¹ * t = (t ^ 3)⁻¹ * s⁻¹ * t ^ 3 * (s ^ 2)⁻¹ := by
    simpa using conj_inv_pow_reorder hsQ hy ht (i := 1) (j := 3) (by decide)
  have h23 : (t ^ 2)⁻¹ * (s ^ 3)⁻¹ * t ^ 2 = (t ^ 3)⁻¹ * (s ^ 2)⁻¹ * t ^ 3 * s⁻¹ := by
    simpa using conj_inv_pow_reorder hsQ hy ht (i := 2) (j := 3) (by decide)
  have e12 : s⁻¹ * t ^ 2 * s⁻¹ = t * (s ^ 2)⁻¹ * t := by
    calc s⁻¹ * t ^ 2 * s⁻¹ = t ^ 2 * ((t ^ 2)⁻¹ * s⁻¹ * t ^ 2 * s⁻¹) := by group
      _ = t ^ 2 * (t⁻¹ * (s ^ 2)⁻¹ * t) := by rw [← h12]
      _ = t * (s ^ 2)⁻¹ * t := by group
  have e13 : s ^ 3 * (t ^ 2)⁻¹ * s⁻¹ = t * s ^ 2 * (t ^ 3)⁻¹ := by
    have h13' : t⁻¹ * s ^ 3 * t = s ^ 2 * (t ^ 3)⁻¹ * s * t ^ 3 := by
      calc t⁻¹ * s ^ 3 * t = (t⁻¹ * (s ^ 3)⁻¹ * t)⁻¹ := by group
        _ = ((t ^ 3)⁻¹ * s⁻¹ * t ^ 3 * (s ^ 2)⁻¹)⁻¹ := by rw [h13]
        _ = s ^ 2 * (t ^ 3)⁻¹ * s * t ^ 3 := by group
    calc s ^ 3 * (t ^ 2)⁻¹ * s⁻¹ = t * (t⁻¹ * s ^ 3 * t) * (t ^ 3)⁻¹ * s⁻¹ := by group
      _ = t * (s ^ 2 * (t ^ 3)⁻¹ * s * t ^ 3) * (t ^ 3)⁻¹ * s⁻¹ := by rw [h13']
      _ = t * s ^ 2 * (t ^ 3)⁻¹ := by group
  have e23 : s ^ 2 = t ^ 3 * s⁻¹ * (t ^ 2)⁻¹ * s ^ 3 * t⁻¹ := by
    have h23' : (t ^ 2)⁻¹ * s ^ 3 * t ^ 2 = s * (t ^ 3)⁻¹ * s ^ 2 * t ^ 3 := by
      calc (t ^ 2)⁻¹ * s ^ 3 * t ^ 2 = ((t ^ 2)⁻¹ * (s ^ 3)⁻¹ * t ^ 2)⁻¹ := by group
        _ = ((t ^ 3)⁻¹ * (s ^ 2)⁻¹ * t ^ 3 * s⁻¹)⁻¹ := by rw [h23]
        _ = s * (t ^ 3)⁻¹ * s ^ 2 * t ^ 3 := by group
    calc s ^ 2 = t ^ 3 * s⁻¹ * (s * (t ^ 3)⁻¹ * s ^ 2 * t ^ 3) * (t ^ 2)⁻¹ * t⁻¹ := by group
      _ = t ^ 3 * s⁻¹ * ((t ^ 2)⁻¹ * s ^ 3 * t ^ 2) * (t ^ 2)⁻¹ * t⁻¹ := by rw [← h23']
      _ = t ^ 3 * s⁻¹ * (t ^ 2)⁻¹ * s ^ 3 * t⁻¹ := by group
  calc s ^ 3 * ((t ^ 2)⁻¹ * (A * B⁻¹) * t ^ 2) * s⁻¹
      = s ^ 3 * (t ^ 2)⁻¹ * s⁻¹ * A * s ^ 2 * B⁻¹ * (s⁻¹ * t ^ 2 * s⁻¹) := by rw [hAB']; group
    _ = s ^ 3 * (t ^ 2)⁻¹ * s⁻¹ * A * (t ^ 3 * s⁻¹ * (t ^ 2)⁻¹ * s ^ 3 * t⁻¹) * B⁻¹
          * (s⁻¹ * t ^ 2 * s⁻¹) := by rw [e23]
    _ = t * s ^ 2 * (t ^ 3)⁻¹ * A * (t ^ 3 * s⁻¹ * (t ^ 2)⁻¹ * s ^ 3 * t⁻¹) * B⁻¹
          * (t * (s ^ 2)⁻¹ * t) := by rw [e13, e12]
    _ = t * (s * ((t ^ 3)⁻¹ * A⁻¹ * t ^ 3) * (s ^ 2)⁻¹)⁻¹ * (t ^ 2)⁻¹
          * (s ^ 2 * (t⁻¹ * B * t) * (s ^ 3)⁻¹)⁻¹ * t := by group

theorem comparison_word_of_normalForms {Q : Subgroup G} [IsMulCommutative Q] {s y t A B : G}
    (hsQ : s ∈ Subgroup.normalizer Q) (hy : y ∈ Q) (ht : t = y⁻¹ * s * y)
    (hAB : (A⁻¹ * s * A) * (B⁻¹ * s * B) = s ^ 2)
    {u₁ u₂ u₃ v₁ v₂ v₃ r₁ r₂ r₃ w₁ w₂ w₃ : G}
    (h₁ : s * ((t ^ 3)⁻¹ * A⁻¹ * t ^ 3) * (s ^ 2)⁻¹ = u₁ * r₁ * v₁)
    (h₂ : s ^ 3 * ((t ^ 2)⁻¹ * (A * B⁻¹) * t ^ 2) * s⁻¹ = u₂ * r₂ * v₂)
    (h₃ : s ^ 2 * (t⁻¹ * B * t) * (s ^ 3)⁻¹ = u₃ * r₃ * v₃)
    (hw₁ : w₁ = t * v₂ * t⁻¹ * u₃) (hw₂ : w₂ = v₃ * (t ^ 2 * u₁ * (t ^ 2)⁻¹))
    (hw₃ : w₃ = v₁ * (t⁻¹ * u₂ * t)) :
    t * r₂⁻¹ * t = w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃ := by
  have key := conj_mul_inv_eq_of_conj_mul_conj_eq_sq hsQ hy ht hAB
  rw [h₁, h₂, h₃] at key
  have hr₂ : r₂ = u₂⁻¹ * (t * (u₁ * r₁ * v₁)⁻¹ * (t ^ 2)⁻¹ * (u₃ * r₃ * v₃)⁻¹ * t) * v₂⁻¹ := by
    rw [← key]; group
  rw [hw₁, hw₂, hw₃, hr₂]; group

theorem comparison_word_of_add_eq_two {F : Type*} [Field F] {P : F → G}
    (hP : ∀ z w : F, P (z + w) = P z * P w) {Q : Subgroup G} [IsMulCommutative Q] {s y t : G}
    (hs : s = P 1) (hsQ : s ∈ Subgroup.normalizer Q) (hy : y ∈ Q) (ht : t = y⁻¹ * s * y)
    {a b : F} (hab : a + b = 2) {ua ub : G}
    (hua : ∀ z : F, ua⁻¹ * P z * ua = P (z * a))
    (hub : ∀ z : F, ub⁻¹ * P z * ub = P (z * b))
    {u₁ u₂ u₃ v₁ v₂ v₃ r₁ r₂ r₃ w₁ w₂ w₃ : G}
    (h₁ : s * ((t ^ 3)⁻¹ * ua⁻¹ * t ^ 3) * (s ^ 2)⁻¹ = u₁ * r₁ * v₁)
    (h₂ : s ^ 3 * ((t ^ 2)⁻¹ * (ua * ub⁻¹) * t ^ 2) * s⁻¹ = u₂ * r₂ * v₂)
    (h₃ : s ^ 2 * (t⁻¹ * ub * t) * (s ^ 3)⁻¹ = u₃ * r₃ * v₃)
    (hw₁ : w₁ = t * v₂ * t⁻¹ * u₃) (hw₂ : w₂ = v₃ * (t ^ 2 * u₁ * (t ^ 2)⁻¹))
    (hw₃ : w₃ = v₁ * (t⁻¹ * u₂ * t)) :
    t * r₂⁻¹ * t = w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃ := by
  refine comparison_word_of_normalForms hsQ hy ht ?_ h₁ h₂ h₃ hw₁ hw₂ hw₃
  have hPa : P a = ua⁻¹ * s * ua := by rw [hs, hua 1, one_mul]
  have hPb : P b = ub⁻¹ * s * ub := by rw [hs, hub 1, one_mul]
  rw [← hPa, ← hPb, ← hP, hab, ← one_add_one_eq_two, hP, hs, pow_two]

end CFSG.FeitThompson
