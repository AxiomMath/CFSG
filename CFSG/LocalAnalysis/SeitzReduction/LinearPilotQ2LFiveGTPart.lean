module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGTOne
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFivePAt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveTThree
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicFourProved
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineLFourFixed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveLabMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRootPart

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem linearTwoFieldKindAtInput_five_of_graph_dual_clauses
    (hcat : SLmCatalogueClausesAt 4)
    (hdet : SLmEvenTypeDetAt 4) (hspor : SporadicFixedLFourTwoInput)
    (hsd : LFiveGraphSylowDataInput) (hc3 : LFiveGraphCosetThreeInput) :
    LinearTwoFieldKindAtInput 5 :=
  linearTwoFieldKindAtInput_five_of_labelDual_field hcat hdet hspor
    (lFiveNotNormalFieldInput_of_parts lFiveSOneSylowPartAtInput lFiveFieldRootStepInput_holds
      lFiveFieldPartInput_holds)
    (lFiveFieldNOneInput_of_transfer (lFiveGraphTransferInput_of_sylowData_of_three hsd hc3))
    linearTwoSwapLabelDualAtInput_five

section Catalogue

theorem linearTwoFieldKindAtInput_five_of_graph_dual (hGLS : GLS3OddLieAutComponentsInput)
    (hsd : LFiveGraphSylowDataInput) (hc3 : LFiveGraphCosetThreeInput) :
    LinearTwoFieldKindAtInput 5 :=
  linearTwoFieldKindAtInput_five_of_graph_dual_clauses
    (slmCatalogueClausesAt_of_gls3_sporadic (by norm_num) hGLS
      (catSLmSporadicAt_of_four_le le_rfl))
    (slmEvenTypeDetAt (by norm_num)) SporadicRefine.sporadicFixedLFourTwoInput hsd hc3

end Catalogue

end CFSG.SeitzReduction.LinearPilot
