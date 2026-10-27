module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueSwap

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Main

theorem seitzExclusion_highPSp_of_inputs_unique (hGLS : GLS3OddLieAutComponentsInput)
    (hX : ∀ m : ℕ, 3 ≤ m → Sp2mNotOddLieInput m) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : ∀ m : ℕ, 3 ≤ m → CatSp2mSporadicResidual m)
    (hFour : SpFourOrthInput) (hGraph : SpGraphRowsInput) (hThree : SpThreeInput)
    (hTwo : SpTwoInput) : SeitzExclusion HighPSp :=
  seitzExclusion_highPSp_of_inputs hGLS hX hMinn hMcomp hres spFieldRowUniqueInput_holds hFour
    spSwapRowUniqueInput_holds hGraph hThree hTwo

end Main

end CFSG.SeitzReduction.SymplecticPilot
