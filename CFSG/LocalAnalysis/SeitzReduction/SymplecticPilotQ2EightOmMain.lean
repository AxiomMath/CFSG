module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmKind

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem spTwoInput_of_open_inputs_eightOm (hcat : ∀ m : ℕ, 3 ≤ m → Sp2mCatalogueClausesAt m)
    (hLE : SpTwoLinearEvenEightAgreeInput) (hUE : SpTwoUnitaryEvenEightAgreeInput)
    (hOPA8 : SpTwoOmegaPlusAlignEightInput) (hOPP8 : SpTwoOmegaPlusPlaceEightInput)
    (hOPB8 : SpTwoOmegaBClassAtInput .omegaPlus 3)
    (hOP : SpTwoOmegaKindInput .omegaPlus) (hOPB : SpTwoOmegaBClassInput .omegaPlus)
    (hOMA8 : SpTwoOmegaMinusAlignEightInput) (hOMP8 : SpTwoOmegaMinusPlaceEightInput)
    (hOMB8 : SpTwoOmegaBClassAtInput .omegaMinus 3)
    (hOM : SpTwoOmegaKindInput .omegaMinus) (hOMB : SpTwoOmegaBClassInput .omegaMinus) :
    SpTwoInput :=
  spTwoInput_of_open_inputs_eightB hcat hLE hUE
    (spTwoOmegaKindEightInput_omegaPlus_of_align_place hOPA8 hOPP8)
    (spTwoOmegaClassEightInput_omegaPlus_of_bClass hOPB8) hOP
    (spTwoOmegaClassInput_of_bClass (Or.inl rfl) hOPB)
    (spTwoOmegaKindEightInput_omegaMinus_of_align_place hOMA8 hOMP8)
    (spTwoOmegaClassEightInput_omegaMinus_of_bClass hOMB8) hOM
    (spTwoOmegaClassInput_of_bClass (Or.inr rfl) hOMB)

end CFSG.SeitzReduction.SymplecticPilot
