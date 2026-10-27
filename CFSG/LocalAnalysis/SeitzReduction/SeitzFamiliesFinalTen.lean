module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeSplitModule
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeTilde
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmpMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmrMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiFinal
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section Base

theorem lFiveGraphMcBrideInput_of_final10 (hT : LinearPilot.LFiveFieldTildeSplitInput) :
    LinearPilot.LFiveGraphMcBrideInput :=
  have hM : LinearPilot.LFiveFieldSylowModelInput :=
    LinearPilot.lFiveFieldSylowModelInput_of_split
      (LinearPilot.lFiveFieldSylowSplitInput_of_tilde hT)
  LinearPilot.lFiveGraphMcBrideInput_of_char
    (LinearPilot.lFiveGraphSylowCharInput_of_chain
      (LinearPilot.lFiveGraphSylowChainInput_of_model hM))
    (LinearPilot.lFiveFieldSylowRadicalInput_of_model hM)

theorem lFiveGraphXCentralInput_of_final10 (hN : LinearPilot.LFiveGraphLeviNormInput) :
    LinearPilot.LFiveGraphXCentralInput :=
  LinearPilot.lFiveGraphXCentralInput_of_leviInput
    (LinearPilot.lFiveGraphLeviInput_of_fieldModule_of_leviNorm
      LinearPilot.lFiveWOneFieldModuleInput_holds hN)

section U3

theorem u3C1OuterSwapHighInput_of_final10 (hSL2 : RankOne.GmiCatSL2CoverInput) :
    RankOne.U3C1OuterSwapHighInput :=
  RankOne.u3C1OuterSwapHighInput_of_gmp_fusion_layer RankOne.u3C1GmsFusionInput_holds
    (RankOne.u3C1GmsLayerInput_of_top CFSG.Goldschmidt.topStatement hSL2)

end U3

end Base

end CFSG.SeitzReduction
