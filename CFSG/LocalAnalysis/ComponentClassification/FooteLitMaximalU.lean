module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def FooteMaximalUnbalancedInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L → FooteMaximal L → FooteType L →
      Blueprint.OddLieType X ∨ CFSG.pRank 2 ↥(coreActionKernel L) = 1 ∨ FooteExceptional X L

theorem footeMaximalUnbalancedInput_of_footeMaximalInput (hF : FooteMaximalInput) :
    FooteMaximalUnbalancedInput := by
  intro X _ _ _ hnonab hK _ _ x _ L hT hLF htype
  exact hF X hnonab hK x hT.1 L hT.2.2.2.1 hT.2.2.2.2.1 hLF htype

end CFSG.ComponentClassification.FooteLit
