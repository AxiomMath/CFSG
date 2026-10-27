module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open Matrix

@[expose] def L34EndFusionStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
    ∃ g : G, g⁻¹ * a * g ∈ S ⊓ J ∧ g⁻¹ * a * g ≠ a

@[expose] def L34EndStructureRestStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
    (∃ g : G, g⁻¹ * a * g ∈ S ⊓ J ∧ g⁻¹ * a * g ≠ a) →
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (T : Subgroup L),
      Nonempty (↥T ≃* Multiplicative (Fin 3 → ZMod 4)) ∧ centralizer (T : Set L) = T ∧
      (∃ φ : L →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧ φ.ker = T) ∧
      ∃ Q : Sylow 2 L, Nonempty (↥S ≃* ↥(Q : Subgroup L))

end CFSG.ComponentClassification.GrSLit
