module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34OrbitInputs

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GrSLit

@[expose] def L34Lemma511CenterStep : Prop := L34Lemma511OrbitStep

@[expose] def L34Lemma511PairStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u = u * s) →
    (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
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
