module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMain
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldCover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotStep3

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.LinearPilot (SLmNotOddLieInputAt CatSLmSporadicAt)

section Main

theorem seitzExclusion_highE6_of_rowInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SLmNotOddLieInputAt 6) (hSpor : CatSLmSporadicAt 6) (hFam : FieldCoverFamilyInput)
    (hEnd : E6FieldEndgameEvenInput) (hSCT : E6SwapRowCTInput) (hSU : E6SwapRowUniqueInput)
    (h2p : E6TwoPositionInput) (h2r : E6TwoRowsInput) : SeitzExclusion (HighExceptional .E6) :=
  seitzExclusion_highE6_of_inputs hGLS hXodd hSpor e6FieldCoverInput_holds hFam
    e6FieldRowStep3Input_holds hEnd hSCT hSU h2p h2r

end Main

end CFSG.SeitzReduction.E6Pilot
