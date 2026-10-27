module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup

@[expose] def OuterL2Config (G : Type) [Group G] (N : Subgroup G) (p f : ℕ) (α : G)
    (J : Subgroup G) : Prop :=
  N.Normal ∧ centralizer (N : Set G) = ⊥ ∧
    (Blueprint.LieModel ↥N .PSL 4 p f ∨ Blueprint.LieModel ↥N .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel ↥N .POmegaMinus 4 p e) ∧
    orderOf α = 2 ∧ α ∉ N ∧ J ≤ centralizer ({α} : Set G) ∧
    IsComponent (J.subgroupOf (centralizer ({α} : Set G))) ∧
    Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p (2 * f) ∧ IsStandardSubgroup J

@[expose] def OuterL2Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ (α : G) (J : Subgroup G), OuterL2Config G N p f α J → J ≤ N →
      ∀ τ : G, τ * α = α * τ → (∀ x ∈ J, τ * x = x * τ) → (∃ k : ℕ, τ ^ 2 ^ k = 1) →
        τ ∈ zpowers α

@[expose] def OuterL2Fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ (α : G) (J : Subgroup G), OuterL2Config G N p f α J → J ≤ N →
      ∀ ζ ∈ J, orderOf ζ = 2 → ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
