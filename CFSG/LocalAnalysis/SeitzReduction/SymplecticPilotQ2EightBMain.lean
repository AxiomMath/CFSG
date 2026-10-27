module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOverlap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBEight
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapRow
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightBUnitaryRow

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem spTwoRowInput_linearEven_of_agree (h : SpTwoLinearEvenEightAgreeInput) :
    SpTwoRowInput .linearEven :=
  spTwoRowInput_linearEven_of_inputs h spTwoLinearEvenSecondClassEightInput_holds
    spTwoLinearEvenSecondClassInput_holds

theorem spTwoInput_of_open_inputs_eightB (hcat : ∀ m : ℕ, 3 ≤ m → Sp2mCatalogueClausesAt m)
    (hLE : SpTwoLinearEvenEightAgreeInput) (hUE : SpTwoUnitaryEvenEightAgreeInput)
    (hOP8 : SpTwoOmegaKindEightInput .omegaPlus) (hOP8' : SpTwoOmegaClassEightInput .omegaPlus)
    (hOP : SpTwoOmegaKindInput .omegaPlus) (hOPc : SpTwoOmegaClassInput .omegaPlus)
    (hOM8 : SpTwoOmegaKindEightInput .omegaMinus) (hOM8' : SpTwoOmegaClassEightInput .omegaMinus)
    (hOM : SpTwoOmegaKindInput .omegaMinus) (hOMc : SpTwoOmegaClassInput .omegaMinus) :
    SpTwoInput := by
  refine spTwoInput_of_catalogue_rows hcat fun κ => ?_
  cases κ with
  | field => exact spTwoRowInput_field_holds
  | swap => exact spTwoRowInput_swap
  | linearEven => exact spTwoRowInput_linearEven_of_agree hLE
  | unitaryEven => exact spTwoRowInput_unitaryEven_of_agree hUE
  | linearOdd => exact spTwoRowInput_linearOdd_holds
  | unitaryOdd => exact spTwoRowInput_unitaryOdd_holds
  | omegaPlus => exact spTwoRowInput_omegaPlus_of_all hOP8 hOP8' hOP hOPc
  | omegaMinus => exact spTwoRowInput_omegaMinus_of_all hOM8 hOM8' hOM hOMc

end CFSG.SeitzReduction.SymplecticPilot
