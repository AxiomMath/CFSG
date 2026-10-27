module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def L34Lemma58OrbitStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S,
    IsSylowTwoIn (S ⊓ centralizer ({u} : Set G))
      (centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G)) →
    (∃ w ∈ omegaOne (S ⊓ coreActionKernel L), w ≠ 1 ∧
      w ∈ ⁅S ⊓ L ⊓ centralizer ({u} : Set G), S ⊓ L ⊓ centralizer ({u} : Set G)⁆) →
    ∀ y ∈ S ⊓ coreActionKernel L, orderOf y = 4 →
    (∀ s ∈ S, s⁻¹ * y⁻¹ * s * y ∈ omegaOne (S ⊓ coreActionKernel L)) →
    ∃ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) ∧
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) ∧
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ ∧
      (¬ (IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁)) ∨
        y ∈ normalizer (K₁ : Set G))

@[expose] def L34NonelementaryCenterCommutatorFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
    (∃ z ∈ P ⊓ zStarIn K, z * z ≠ 1) →
    ∃ a ∈ P, a * a = 1 ∧ a ∉ zStarIn K ∧ ∃ w ∈ P ⊓ zStarIn K, w ≠ 1 ∧ w * w = 1 ∧
      w ∈ ⁅P ⊓ centralizer ({a} : Set G), P ⊓ centralizer ({a} : Set G)⁆

end CFSG.ComponentClassification.GrSLit
