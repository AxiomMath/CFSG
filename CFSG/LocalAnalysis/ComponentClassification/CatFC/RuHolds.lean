module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.RuFi23
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableMonster
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableRu

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC


theorem catalogNoRu_holds : EvenSporadicStandard.Induction.Balance.CatalogNoRu :=
  catalogNoRu_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
    (fun _ _ h => CatLeaf.involutionCentralizersComponentFree_of_evenLieType h)
    CatLeafProof.evenLieOuterTwoComponentsInput_holds
    CatLeafProof.lieOrderFormulasInput
    GSThmB.QPUSpor.card_carrier_eq_sporOrder
    sporadic_rows_ru sporadic_rows_m

end CFSG.ComponentClassification.CatFC
