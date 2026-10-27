module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

variable {C : Type*} [Group C]

structure LineSplit (Z : Subgroup C) (F : Type*) [Field F] (ι₁ ι₂ : F → C) (P : C → Prop) :
    Prop where
  map_add₁ : ∀ x y, ι₁ (x + y) = ι₁ x * ι₁ y
  map_add₂ : ∀ x y, ι₂ (x + y) = ι₂ x * ι₂ y
  inj₁ : ∀ x, ι₁ x = 1 → x = 0
  inj₂ : ∀ x, ι₂ x = 1 → x = 0
  comm : ∀ x y, Commute (ι₁ x) (ι₂ y)
  inf : ∀ x y, ι₁ x = ι₂ y → x = 0
  mem_iff : ∀ z, z ∈ Z ↔ ∃ d, z = ι₁ d * ι₂ d
  prop₁ : ∀ x, x ≠ 0 → P (ι₁ x)
  prop₂ : ∀ x, x ≠ 0 → P (ι₂ x)
  scalar : ∀ c : F, c ≠ 0 → ∃ a : C, ∀ x, a⁻¹ * ι₁ x * a = ι₁ x ∧ a⁻¹ * ι₂ x * a = ι₂ (c * x)

namespace LineSplit

variable {Z : Subgroup C} {F : Type*} [Field F] {ι₁ ι₂ : F → C} {P : C → Prop}
  (h : LineSplit Z F ι₁ ι₂ P)
include h

theorem map_zero₁ : ι₁ 0 = 1 := by
  have h0 := h.map_add₁ 0 0
  rw [add_zero] at h0
  exact (mul_eq_left.1 h0.symm)

theorem map_zero₂ : ι₂ 0 = 1 := by
  have h0 := h.map_add₂ 0 0
  rw [add_zero] at h0
  exact (mul_eq_left.1 h0.symm)

theorem mul_self₁ [CharP F 2] (x : F) : ι₁ x * ι₁ x = 1 := by
  rw [← h.map_add₁, CharTwo.add_self_eq_zero, h.map_zero₁]

theorem mul_self₂ [CharP F 2] (x : F) : ι₂ x * ι₂ x = 1 := by
  rw [← h.map_add₂, CharTwo.add_self_eq_zero, h.map_zero₂]

end LineSplit

end CFSG.ComponentClassification.RankTwoExceptional.Exc
