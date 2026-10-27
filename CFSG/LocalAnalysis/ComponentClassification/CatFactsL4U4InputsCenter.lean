module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup

@[expose] def CenterSylowConfig (G : Type) [Group G] (N : Subgroup G) (α : G) (J R : Subgroup G)
    (τ : G) : Prop :=
  N.Normal ∧ centralizer (N : Set G) = ⊥ ∧ orderOf α = 2 ∧ J ≤ centralizer ({α} : Set G) ∧
    IsComponent (J.subgroupOf (centralizer ({α} : Set G))) ∧ IsStandardSubgroup J ∧
    R ≤ N ⊓ normalizer (J : Set G) ∧ R ≤ centralizer ({α} : Set G) ∧
    (∃ R' : Sylow 2 ↥(N ⊓ normalizer (J : Set G)),
      (R' : Subgroup _) = R.subgroupOf (N ⊓ normalizer (J : Set G))) ∧
    τ * α = α * τ ∧ (∀ x ∈ J, τ * x = x * τ) ∧ (∀ r ∈ R, τ * r = r * τ) ∧
    ∃ k : ℕ, τ ^ 2 ^ k = 1

@[expose] def CenterSylowAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) (α : G) (J R : Subgroup G) (τ : G),
    CenterSylowConfig G N α J R τ →
    ∀ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) → Nonempty (↥N ≃* alternatingGroup (Fin (n + 4))) →
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin n)) → τ ∈ zpowers α

@[expose] def CenterSylowLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) (α : G) (J R : Subgroup G) (τ : G),
    CenterSylowConfig G N α J R τ →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → α ∈ N → J ≤ N →
      (Blueprint.LieModel ↥N .PSL 4 p f ∨ Blueprint.LieModel ↥N .PSU 4 p f ∨
        ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel ↥N .POmegaMinus 4 p e) →
      Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p (2 * f) → τ ∈ zpowers α

@[expose] def CenterSylowSuz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) (α : G) (J R : Subgroup G) (τ : G),
    CenterSylowConfig G N α J R τ → Nonempty (↥N ≃* Blueprint.NativeSporadic.Suz) →
      Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 3 2 2 → τ ∈ zpowers α

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
