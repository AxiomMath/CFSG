module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.RuFi23
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24CSelfCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadicFi
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableFi
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableMonster

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC


theorem catalogFi23Host_holds : EvenSporadicStandard.Induction.Balance.CatalogFi23Host :=
  catalogFi23Host_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
    (fun _ _ h => CatLeaf.involutionCentralizersComponentFree_of_evenLieType h)
    CatLeafProof.evenLieOuterTwoComponentsInput_holds
    CatLeafProof.lieOrderFormulasInput
    GSThmB.QPUSpor.card_carrier_eq_sporOrder
    (EvenSporadicStandard.Induction.Fi.V3.fi23SelfCentralizing_of_mult
      (EvenSporadicStandard.Induction.fi23Mult_of_sporadicMultipliers
        RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
    sporadic_rows_fi23 sporadic_rows_fi24 sporadic_rows_b sporadic_rows_m

end CFSG.ComponentClassification.CatFC
