module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315SzR2

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

abbrev gmsR₀ (L T R₂ : Subgroup G) : Subgroup G := (T ⊓ L) ⊔ R₂

namespace Sec3

variable {L T R R₂ U : Subgroup G} {a : ℕ} {y d : G}

namespace SzR

variable (hS : SzR G L T R a y d)
include hS

theorem commutator_mem_gmsA
    (h34 : NoStronglyClosedAbelian G) {x x' : G} (hx : x ∈ R) (hx' : x' ∈ R) :
    x * x' * x⁻¹ * x'⁻¹ ∈ gmsA L T := by
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  exact hS.commutator_mem_gmsA_of_isX h34 hX hx hx'

theorem le_normalizer_T₁
    (h34 : NoStronglyClosedAbelian G) : R ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  intro r hr
  refine mem_normalizer_of_conj_mem_of_finite fun t ht => ?_
  have h1 := hS.commutator_mem_gmsA h34 hr (hS.T_le (mem_inf.mp ht).1)
  have e : r * t * r⁻¹ = (r * t * r⁻¹ * t⁻¹) * t := by group
  rw [e]
  exact mul_mem (mem_inf.mp h1).1 ht

theorem exists_mul_of_mem_R
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d) {x : G} (hx : x ∈ R) :
    ∃ x₀ ∈ gmsR₀ L T R₂, ∃ s ∈ T ⊓ centralizer (L : Set G), x₀ * s = x := by
  have hx' : x ∈ R₂ ⊔ T := by rw [sup_comm, hR₂.sup_eq]; exact hx
  obtain ⟨r, hr, t, ht, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (hR₂.le_R.trans hS.le_normalizer_T) hx'
  obtain ⟨t₁, ht₁, s, hs, rfl⟩ := hS.exists_mul_of_mem_T ht
  have hrt : t₁⁻¹ * r * t₁ ∈ R₂ := by
    have h1 := hS.commutator_mem_gmsA h34 (inv_mem (hS.T_le (mem_inf.mp ht₁).1)) (hR₂.le_R hr)
    have e : t₁⁻¹ * r * t₁ = (t₁⁻¹ * r * t₁⁻¹⁻¹ * r⁻¹) * r := by group
    rw [e]
    exact mul_mem (hR₂.gmsA_le h1) hr
  refine ⟨t₁ * (t₁⁻¹ * r * t₁), mul_mem (mem_sup_left ht₁) (mem_sup_right hrt), s, hs, ?_⟩
  group

theorem le_normalizer_R₂
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d) :
    R ≤ normalizer (R₂ : Set G) := by
  intro x hx
  refine mem_normalizer_of_conj_mem_of_finite fun r hr => ?_
  have h1 := hS.commutator_mem_gmsA h34 hx (hR₂.le_R hr)
  have e : x * r * x⁻¹ = (x * r * x⁻¹ * r⁻¹) * r := by group
  rw [e]
  exact mul_mem (hR₂.gmsA_le h1) hr

end SzR

end Sec3

end CFSG.ComponentClassification.GMS78
