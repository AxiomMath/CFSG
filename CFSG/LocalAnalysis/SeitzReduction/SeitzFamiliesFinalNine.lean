module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalEight
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6EdgeMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGTPart
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoEnd
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveUniMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeLSevenOrth
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenBAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUPMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlDMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaClosMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightSiegRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLAgreeAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOnAlignMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOnAlignPlus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEMain

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem lFiveGraphCosetThreeInput_of_final9
    (hX : LinearPilot.LFiveGraphXInput ∨ LinearPilot.LFiveGraphXCentralInput) :
    LinearPilot.LFiveGraphCosetThreeInput :=
  hX.elim LinearPilot.lFiveGraphCosetThreeInput_of_xInput
    LinearPilot.lFiveGraphCosetThreeInput_of_xCentralInput

section Two

theorem seitzExclusion_highF4_of_final9 (hGLS : GLS3OddLieAutComponentsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_final8 hGLS F4Pilot.twoE6RelayEdgeInput_holds
    (F4Pilot.twoTwistedE6RelayInput_of_edgeInput F4Pilot.twoTwistedE6RelayEdgeInput_holds)

theorem spTwoInput_of_final9 (hGLS : GLS3OddLieAutComponentsInput)
    (hclos4 : SymplecticPilot.SpTwoLagDerivedClosureAt 4 2) : SymplecticPilot.SpTwoInput :=
  SymplecticPilot.spTwoInput_of_open_inputs_eightOm (sp2mCatalogueClausesAt_of_gls3 hGLS)
    SymplecticPilot.spTwoLinearEvenEightAgreeInput_holds
    SymplecticPilot.spTwoUnitaryEvenEightAgreeInput_holds
    SymplecticPilot.spTwoOmegaPlusAlignEightInput_holds
    SymplecticPilot.spTwoOmegaPlusPlaceEightInput_holds
    (SymplecticPilot.spTwoOmegaBClassAtInput_three_of_derived (Or.inl rfl) hclos4)
    SymplecticPilot.spTwoOmegaKindInput_omegaPlus_holds
    (SymplecticPilot.spTwoOmegaBClassInput_of_lagClosure (Or.inl rfl)
      SymplecticPilot.spTwoLagClosureInput_holds)
    SymplecticPilot.spTwoOmegaMinusAlignEightInput_holds
    SymplecticPilot.spTwoOmegaMinusPlaceEightInput_holds
    (SymplecticPilot.spTwoOmegaBClassAtInput_three_of_derived (Or.inr rfl) hclos4)
    SymplecticPilot.spTwoOmegaKindInput_omegaMinus_holds
    (SymplecticPilot.spTwoOmegaBClassInput_of_lagClosure (Or.inr rfl)
      SymplecticPilot.spTwoLagClosureInput_holds)

section PSp

theorem spThreeGraphRowsInput_of_final9 (hGLS : GLS3OddLieAutComponentsInput) :
    SymplecticPilot.SpThreeGraphRowsInput :=
  spThreeGraphRowsInput_of_final8 hGLS
    (SymplecticPilot.spThreeLinearOddStandardInput_of_clauses
      (slmCatalogueClausesAt_three_of_gls3 hGLS) (LinearPilot.slmEvenTypeDetAt le_rfl))
    SymplecticPilot.spThreeLinearOddTrivialSiegelInput_holds
    SymplecticPilot.spThreeUnitaryOddOrthInput_holds
    SymplecticPilot.spThreeUnitaryOddSiegelAlignInput_holds

theorem spThreeInput_of_final9 (hGLS : GLS3OddLieAutComponentsInput) :
    SymplecticPilot.SpThreeInput :=
  spThreeInput_of_final6 hGLS (spThreeGraphRowsInput_of_final9 hGLS)

theorem seitzExclusion_highPSp_of_final9 (hGLS : GLS3OddLieAutComponentsInput)
    (hclos4 : SymplecticPilot.SpTwoLagDerivedClosureAt 4 2) : SeitzExclusion HighPSp :=
  seitzExclusion_highPSp_of_final4 hGLS (spGraphRowsInput_of_final7 hGLS)
    (spThreeInput_of_final9 hGLS) (spTwoInput_of_final9 hGLS hclos4)

section LFive

theorem linearTwoFieldKindAtInput_five_of_final9 (hGLS : GLS3OddLieAutComponentsInput)
    (hA : LinearPilot.LFiveFieldSylowNormalInput) (hC : LinearPilot.LFiveGraphMcBrideInput)
    (hX : LinearPilot.LFiveGraphXInput ∨ LinearPilot.LFiveGraphXCentralInput) :
    LinearPilot.LinearTwoFieldKindAtInput 5 :=
  LinearPilot.linearTwoFieldKindAtInput_five_of_graph_dual hGLS
    (LinearPilot.lFiveGraphSylowDataInput_of_inputs hA LinearPilot.lFiveThompsonFieldInput_holds hC)
    (lFiveGraphCosetThreeInput_of_final9 hX)

end LFive

end PSp

end Two

end CFSG.SeitzReduction
