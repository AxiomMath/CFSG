module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def L34Cor217Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G →
    ∀ (a x : G) (J : Subgroup G), GSMaximalUnbalancingTriple a x J →
      IsL34Type (J ⧸ Open.fusionZStar J) → GSWeakMaximalComponent J

@[expose] def L34Cor217ComponentStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ S ⊓ L ⊔ zpowers t, orderOf u = 2 →
    ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL34Type (K₁ ⧸ Open.fusionZStar K₁) → GSWeakMaximalComponent K₁

@[expose] def L34Sec5ComponentInvariantStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ S ⊓ L ⊔ zpowers t, orderOf u = 2 →
    ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL34Type (K₁ ⧸ Open.fusionZStar K₁) →
      S ⊓ centralizer ({u} : Set G) ≤ normalizer (K₁ : Set G)

end CFSG.ComponentClassification.GrSLit
