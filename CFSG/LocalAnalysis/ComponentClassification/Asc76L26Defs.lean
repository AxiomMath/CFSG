module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.Asc76

variable {G : Type*} [Group G]

@[expose] def gammaSet (S : Subgroup G) (Δ : Set (Subgroup G)) : Set G :=
  {x | x ≠ 1 ∧ ∃ T ∈ Δ, T ≤ S ∧ x ∈ T}

@[expose] def fusionGen (Γ : Set G) : Subgroup G :=
  closure {g | ∃ x ∈ Γ, g⁻¹ * x * g ∈ Γ}

@[expose] def Asc76Lemma26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G) (Δ : Set (Subgroup G)),
    IsSylowOf 2 S ⊤ → (∀ T ∈ Δ, IsPGroup 2 T) → (∀ T ∈ Δ, ∀ g : G, rightConjugate T g ∈ Δ) →
    fusionStronglyClosed (gammaSet S Δ) S →
    (∀ T₁ ∈ Δ, ∀ T₂ ∈ Δ, T₁ ≤ S → T₂ ≤ S → T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥) →
    ∀ R ∈ Δ, R ≤ S → 1 < Open.pRank 2 R → ¬ IsElemAbelian 2 R →
      fusionGen (gammaSet S Δ) = ⊤ ∨
        ((∀ R' ∈ Δ, R' ≤ S → 1 < Open.pRank 2 R' → ¬ IsElemAbelian 2 R' → R' = R) ∧
          IsSylowOf 2 R (normalClosure (R : Set G)) ∧
          IsSzOrU3 (↥(normalClosure (R : Set G)) ⧸
            CFSG.Assembly.oddCore ↥(normalClosure (R : Set G))))

@[expose] def Asc76Lemma27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G) (Δ : Set (Subgroup G)),
    IsSylowOf 2 S ⊤ → (∀ T ∈ Δ, IsCyclic T ∧ Nat.card T = 4) →
    (∀ T ∈ Δ, ∀ g : G, rightConjugate T g ∈ Δ) →
    fusionStronglyClosed (gammaSet S Δ) S →
    (∀ T₁ ∈ Δ, ∀ T₂ ∈ Δ, T₁ ≤ S → T₂ ≤ S → T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥) →
    (∃ V : Subgroup G, Nat.card V = 4 ∧ IsElemAbelian 2 V ∧
      ∀ v ∈ V, v ≠ 1 → v ∈ gammaSet S Δ) →
    fusionGen (gammaSet S Δ) = ⊤

end CFSG.ComponentClassification.Asc76.L26
