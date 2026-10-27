module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTables
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainOdd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Inputs

theorem fieldNeighbourInput_holds : FieldNeighbourInput := by
  intro G _ _ L K₂ _ _ _ σ f hq hf e t hw N hN h
  exact ⟨nonempty_levi_mulEquiv_neighbourCore hw hf e hN h K₂ hq.card_eq,
    perfectCore_neighbourCore_inf_centralizer_eq hw hf e hN⟩

theorem swapNeighbourInput_holds : SwapNeighbourInput :=
  fun _ _ _ _ _ _ _ _ e _ _ hw hf _ hN h => exists_swapDecomposition hw hf e hN h

theorem fieldSwapPieceTablesInput_holds : FieldSwapPieceTablesInput :=
  fieldSwapPieceTablesInput_of_inputs fieldNeighbourInput_holds swapNeighbourInput_holds

end Inputs

section Main

theorem seitzExclusion_highF4_of_rowInputs' (hGLS : GLS3OddLieAutComponentsInput)
    (hSp6Odd : Sp6NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual)
    (hGr : GraphPieceTablesInput) (hFU : FieldRowUniqueOddInput) (hSU : SwapRowUniqueInput)
    (hECT : E6RowCTQuotInput) (hEU : E6RowUniqueQuotInput) (hTCT : TwistedE6RowCTQuotInput)
    (hTU : TwistedE6RowUniqueQuotInput) (h2 : TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_inputs' hGLS hSp6Odd hMinn hMcomp hres hr8YInput_holds
    fieldSwapPieceTablesInput_holds hGr fieldNeighbourInput_holds hFU swapRowCTInput_holds hSU hECT
    hEU hTCT hTU h2

end Main

end CFSG.SeitzReduction.F4Pilot
