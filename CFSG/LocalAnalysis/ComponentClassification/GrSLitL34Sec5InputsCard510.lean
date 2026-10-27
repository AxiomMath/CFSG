module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34Lemma510CentralCardStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → (∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1) →
    (∃ z : G, orderOf z = 2 ∧ z ≠ t ∧
      omegaOne (S ⊓ coreActionKernel L) = zpowers t ⊔ zpowers z) →
    (∃ y ∈ S ⊓ coreActionKernel L ⊓ L, ∃ s ∈ S, s * y ≠ y * s) →
    ∃ y ∈ S ⊓ L, y ∉ zStarIn L ∧ y * y = 1 ∧ (∀ s ∈ S, s * y = y * s) ∧
      ∀ z' ∈ S ⊓ coreActionKernel L ⊓ L,
        Nat.card ↥(oddIn L ⊓ centralizer ({y * z'} : Set G)) ≤
          Nat.card ↥(oddIn L ⊓ centralizer ({y} : Set G))

end CFSG.ComponentClassification.GrSLit
