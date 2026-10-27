module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartnerClass
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapMain
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert

public section

namespace CFSG.SeitzReduction

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Small

theorem seitzExclusion_highPSL_of_xchar (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : LinearPilot.CatSLmSporadic) (hTwo : LinearPilot.LinearTwoInput) :
    SeitzExclusion HighPSL :=
  LinearPilot.seitzExclusion_highPSL_of_cat_inputs hGLS CrossChar.sLmNotOddLieInput hSpor hTwo

end Small

section Large

theorem seitzExclusion_highF4_of_xchar_caseL (hGLS : GLS3OddLieAutComponentsInput)
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    (hres : F4Pilot.CatSp6SporadicResidual) (hGr : F4Pilot.GraphPieceTablesInput)
    (hECT : F4Pilot.E6RowCTQuotInput) (hEL : F4Pilot.E6RowXiCaseLInput)
    (hTCT : F4Pilot.TwistedE6RowCTQuotInput) (hTL : F4Pilot.TwistedE6RowXiCaseLInput)
    (h2 : F4Pilot.TwoRowsInput) : SeitzExclusion (HighExceptional .F4) :=
  F4Pilot.seitzExclusion_highF4_of_caseL hGLS CrossChar.sp6NotOddLieInput hMinn hMcomp hres hGr
    hECT hEL hTCT hTL h2

theorem seitzExclusion_highE8_of_xchar (hGLS : GLS3OddLieAutComponentsInput)
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    (h2 : E8Pilot.E8TwoInput) : SeitzExclusion (HighExceptional .E8) :=
  E8Pilot.seitzExclusion_highE8_of_inputs''' hGLS CrossChar.e7NotOddLieInput hMinn hMcomp h2

end Large

end CFSG.SeitzReduction
