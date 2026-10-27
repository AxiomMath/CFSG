module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Swap
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Field
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Xi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourMain

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Main

theorem seitzExclusion_highF4_of_graphRowInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hSp6Odd : Sp6NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual)
    (hGr : GraphPieceTablesInput) (hECT : E6RowCTQuotInput) (hEU : E6RowUniqueQuotInput)
    (hTCT : TwistedE6RowCTQuotInput) (hTU : TwistedE6RowUniqueQuotInput) (h2 : TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_rowInputs' hGLS hSp6Odd hMinn hMcomp hres hGr
    fieldRowUniqueOddInput_holds swapRowUniqueInput_holds hECT hEU hTCT hTU h2

theorem seitzExclusion_highF4_of_xiInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hSp6Odd : Sp6NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual)
    (hGr : GraphPieceTablesInput) (hECT : E6RowCTQuotInput) (hEξ : E6RowXiExclusionInput)
    (hTCT : TwistedE6RowCTQuotInput) (hTin : TwistedE6RowInnerInput)
    (hTξ : TwistedE6RowXiExclusionInput) (h2 : TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_graphRowInputs hGLS hSp6Odd hMinn hMcomp hres hGr hECT
    (e6RowUniqueQuotInput_of_xi hEξ) hTCT (twistedE6RowUniqueQuotInput_of_xi hTin hTξ) h2

end Main

end CFSG.SeitzReduction.F4Pilot
