module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section SwapRow

theorem e7SwapRowCTInput_holds : E7SwapRowCTInput := by
  intro G _ _ L K _ _ _ e t f hw hf hX
  exact swapRowCT_E7 hw hf e hX

theorem SwapUnique.e7SwapRowUniqueInput_holds : E7SwapRowUniqueInput := by
  intro G _ _ L K _ _ _ e t f hw hf _ G₁ he₁ h₁₂ hsup g hg
  exact SwapUnique.swapRowUnique_E7 hw hf e he₁ h₁₂ hsup g hg

end SwapRow

section Main

theorem seitzExclusion_highE7_of_five_inputs
    (hGLS : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    (hFam : E7FieldRowFamilyInput) (h2 : E7TwoInput) :
    SeitzExclusion (HighExceptional .E7) :=
  seitzExclusion_highE7_of_inputs hGLS hXodd hSpor hFam e7SwapRowCTInput_holds
    SwapUnique.e7SwapRowUniqueInput_holds h2

end Main

end CFSG.SeitzReduction.E7Pilot
