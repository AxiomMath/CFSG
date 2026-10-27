module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqElem

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit

@[expose] def L34Lemma511OrbitStepC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u = u * s) →
    (∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁)) →
    ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      ∀ s₂ ∈ S, ∀ s₃ ∈ S, ∀ s₄ ∈ S, conjugate K₁ s₂ ≠ K₁ → conjugate K₁ s₃ ≠ K₁ →
        conjugate K₁ s₄ ≠ K₁ → conjugate K₁ s₃ ≠ conjugate K₁ s₂ →
        conjugate K₁ s₄ ≠ conjugate K₁ s₂ → conjugate K₁ s₄ ≠ conjugate K₁ s₃ →
        ∀ e₁ ∈ S ⊓ K₁, orderOf e₁ = 2 →
          ¬ S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ≤
            closure (conjSet S e₁) ⊔ S ⊓ coreActionKernel L

@[expose] def L34Lemma511PairStepC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u = u * s) →
    (∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁)) →
    ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      ∀ s ∈ S, conjugate K₁ s ≠ K₁ →
        (∀ s' ∈ S, conjugate K₁ s' = K₁ ∨ conjugate K₁ s' = conjugate K₁ s) →
        ∀ e₁ ∈ S ⊓ K₁, orderOf e₁ = 2 → Nat.card ↥(S ⊓ K₁) = 2 → e₁ ∉ coreActionKernel L →
          e₁ ∈ S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊔ S ⊓ coreActionKernel L →
          False

end CFSG.ComponentClassification.HSFLit.L34Uniq
