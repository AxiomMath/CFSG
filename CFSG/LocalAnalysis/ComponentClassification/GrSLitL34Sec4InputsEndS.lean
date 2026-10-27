module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open Matrix

@[expose] def L34SylowCenterCyclicFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 →
    ∀ u ∈ P, (∀ p ∈ P, u * p = p * u) → u ∈ zStarIn J

@[expose] def L34EndStructureStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (T : Subgroup L),
      Nonempty (↥T ≃* Multiplicative (Fin 3 → ZMod 4)) ∧ centralizer (T : Set L) = T ∧
      (∃ φ : L →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧ φ.ker = T) ∧
      ∃ Q : Sylow 2 L, Nonempty (↥S ≃* ↥(Q : Subgroup L))

@[expose] def FourCubeSylowFact : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (T : Subgroup L),
    Nonempty (↥T ≃* Multiplicative (Fin 3 → ZMod 4)) → centralizer (T : Set L) = T →
    (∃ φ : L →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧ φ.ker = T) →
    ∀ Q : Sylow 2 L,
      (∃ R : Sylow 2 Blueprint.NativeSporadic.HS,
          Nonempty (↥(Q : Subgroup L) ≃* ↥(R : Subgroup Blueprint.NativeSporadic.HS))) ∨
        ∃ R : Sylow 2 Blueprint.NativeSporadic.ON,
          Nonempty (↥(Q : Subgroup L) ≃* ↥(R : Subgroup Blueprint.NativeSporadic.ON))

@[expose] def L34EndTypeStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    ∀ P : Sylow 2 G, (P : Subgroup G) = S →
      (∃ T : Sylow 2 Blueprint.NativeSporadic.HS,
          Nonempty ((P : Subgroup G) ≃* (T : Subgroup Blueprint.NativeSporadic.HS))) ∨
        ∃ T : Sylow 2 Blueprint.NativeSporadic.ON,
          Nonempty ((P : Subgroup G) ≃* (T : Subgroup Blueprint.NativeSporadic.ON))

end CFSG.ComponentClassification.GrSLit
