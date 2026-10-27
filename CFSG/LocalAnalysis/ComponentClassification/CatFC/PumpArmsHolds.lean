module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTable
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
public import CFSG.Open.MonsterY443Finiteness

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC


theorem armInputs_holds : ArmInputs :=
  { gls := SeitzReduction.gls3OddLieAutComponentsInput
    evenInner := fun _ _ h => CatLeaf.involutionCentralizersComponentFree_of_evenLieType h
    evenOuter := CatLeafProof.evenLieOuterTwoComponentsInput_holds
    order := CatLeafProof.lieOrderFormulasInput
    card := GSThmB.QPUSpor.card_carrier_eq_sporOrder
    table := by
      intro _ _ _ hS hna _ e _ hσ _ hD
      exact sporadic_comp_order CFSG.Open.Open.monster_y443_derived_card hS hna e hσ hD }

end CFSG.ComponentClassification.CatFC
