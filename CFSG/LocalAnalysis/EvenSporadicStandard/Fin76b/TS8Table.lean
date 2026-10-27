module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Solomon

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def OuterTable {X : Type*} [Group X] (ζ α t g₁ g₂ h₁ h₂ : X) : Prop :=
  ζ * ζ = 1 ∧ α * α = 1 ∧ t * t = 1 ∧ α ≠ 1 ∧ t ≠ 1 ∧ α ≠ t ∧ α * t = t * α ∧
    ζ * α * ζ⁻¹ = α * t ∧ ζ * t * ζ⁻¹ = t ∧ h₁ = ζ * g₁ * ζ⁻¹ ∧ h₂ = ζ * g₂ * ζ⁻¹ ∧
    IsPGroup 2 (Subgroup.closure ({α, t, g₁, g₂, h₁, h₂} : Set X)) ∧
    (∀ c ∈ ({g₁, g₂, h₁, h₂} : Set X), c * α = α * c ∧ c * t = t * c) ∧
    (g₁ * g₁ = 1 ∨ g₁ * g₁ = t) ∧ (g₂ * g₂ = 1 ∨ g₂ * g₂ = t) ∧
    g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = α * t ∧ h₁ * h₂ * h₁⁻¹ * h₂⁻¹ = α ∧
    g₁ * h₂ * g₁⁻¹ * h₂⁻¹ = t ∧ g₂ * h₁ * g₂⁻¹ * h₁⁻¹ = t ∧ g₁ * h₁ = h₁ * g₁ ∧ g₂ * h₂ = h₂ * g₂

@[expose] def OuterNoTable : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (z α t g₁ g₂ h₁ h₂ : K),
    Lemma96Conclusion K (QuotientGroup.mk z) → OuterTable z α t g₁ g₂ h₁ h₂ →
      (∀ k : K, k * z * k⁻¹ ≠ α) → False

@[expose] def OuterTableU43 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* ↥U43Ext) →
    ∀ ζ α t g₁ g₂ h₁ h₂ : X, OuterTable ζ α t g₁ g₂ h₁ h₂ → ∃ k : X, k * ζ * k⁻¹ = α

@[expose] def OuterTableWreath : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X), N.Normal →
    Nonempty (↥N ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) →
    centralizer (N : Set X) = ⊥ →
    ∀ ζ α t g₁ g₂ h₁ h₂ : X, OuterTable ζ α t g₁ g₂ h₁ h₂ → False

end CFSG.EvenSporadicStandard.Fin76b
