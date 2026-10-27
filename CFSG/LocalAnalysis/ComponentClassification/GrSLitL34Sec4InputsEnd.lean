module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs47

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def ONanSylowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ (S : Sylow 2 G) (T : Sylow 2 Blueprint.NativeSporadic.ON),
      Nonempty ((S : Subgroup G) ≃* (T : Subgroup Blueprint.NativeSporadic.ON)) →
      Nonempty (G ≃* Blueprint.NativeSporadic.ON)

@[expose] def L34EndSylowStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    ∃ P : Sylow 2 G, (P : Subgroup G) = S ∧
      ((∃ T : Sylow 2 Blueprint.NativeSporadic.HS,
          Nonempty ((P : Subgroup G) ≃* (T : Subgroup Blueprint.NativeSporadic.HS))) ∨
        ∃ T : Sylow 2 Blueprint.NativeSporadic.ON,
          Nonempty ((P : Subgroup G) ≃* (T : Subgroup Blueprint.NativeSporadic.ON)))

end CFSG.ComponentClassification.GrSLit
