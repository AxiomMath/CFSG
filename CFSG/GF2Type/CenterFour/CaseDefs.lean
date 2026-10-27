module

public import CFSG.GF2Type.CenterFour.Setting

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup

variable {G : Type} [Group G]

@[expose] def Fused (z w : G) : Prop := ∃ g : G, g⁻¹ * z * g = w

@[expose] def CaseA [Finite G] (z : G) : Prop :=
  ∀ w : G, Fused z w → w ∈ centralizer ({z} : Set G) → w ∈ centralizer (centerAt z : Set G)

theorem Fused.refl (z : G) : Fused z z := ⟨1, by simp⟩

theorem Fused.trans {z w v : G} (h₁ : Fused z w) (h₂ : Fused w v) : Fused z v := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  exact ⟨g₁ * g₂, by simp [mul_assoc]⟩

theorem Fused.symm {z w : G} (h : Fused z w) : Fused w z := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g⁻¹, by simp [mul_assoc]⟩

theorem fused_conj (z g : G) : Fused z (g⁻¹ * z * g) := ⟨g, rfl⟩

theorem Fused.conj_iff {z w g : G} : Fused (g⁻¹ * z * g) w ↔ Fused z w := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨g * k, by simp [mul_assoc]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨g⁻¹ * k, by simp [mul_assoc]⟩

end CFSG.GF2Type.CenterFour
