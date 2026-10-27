module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup

public section

open Subgroup

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

structure FusedCfg {A : Type*} [Group A] (K₁ K₂ S : Subgroup A) (F : Type) [Field F] : Prop where
  e₁ : Nonempty (↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  e₂ : Nonempty (↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  card_inf : Nat.card ↥(K₁ ⊓ K₂) = 2
  cen₁ : ∀ x ∈ K₁, (∀ y ∈ K₁, x * y = y * x) → x ∈ K₂
  cen₂ : ∀ x ∈ K₂, (∀ y ∈ K₂, x * y = y * x) → x ∈ K₁
  pgroup : IsPGroup 2 ↥S
  norm : S ≤ normalizer ((K₁ ⊔ K₂ : Subgroup A) : Set A)
  card₁ : Nat.card ↥(S ⊓ K₁) = 8
  card₂ : Nat.card ↥(S ⊓ K₂) = 8
  prod : S ⊓ (K₁ ⊔ K₂) = (S ⊓ K₁) ⊔ (S ⊓ K₂)
  z_ex : ∃ z : A, z ∈ K₁ ⊓ K₂ ∧ orderOf z = 2 ∧ z ∈ S ∧ ∀ s ∈ S, s * z = z * s

namespace FusedCfg

variable {A : Type*} [Group A] {K₁ K₂ S : Subgroup A} {F : Type} [Field F]

theorem swap (h : FusedCfg K₁ K₂ S F) : FusedCfg K₂ K₁ S F where
  e₁ := h.e₂
  e₂ := h.e₁
  comm a ha b hb := (h.comm b hb a ha).symm
  card_inf := by rw [inf_comm]; exact h.card_inf
  cen₁ := h.cen₂
  cen₂ := h.cen₁
  pgroup := h.pgroup
  norm := by rw [sup_comm K₂ K₁]; exact h.norm
  card₁ := h.card₂
  card₂ := h.card₁
  prod := by rw [sup_comm K₂ K₁, sup_comm (S ⊓ K₂) (S ⊓ K₁)]; exact h.prod
  z_ex := by
    obtain ⟨z, hz, ho, hS, hc⟩ := h.z_ex
    exact ⟨z, by rw [inf_comm]; exact hz, ho, hS, hc⟩

end FusedCfg

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
