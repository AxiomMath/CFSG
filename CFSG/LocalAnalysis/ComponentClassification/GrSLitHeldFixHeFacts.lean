module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowAll

public section

namespace CFSG.ComponentClassification.GrSLit

theorem heldSylowElementarySixtyFour : HeldSylowElementarySixtyFour :=
  fun _ hT hcard => HeldFix.sylow_elementary_sixtyFour hT hcard

theorem heldSylowCenterTwo : HeldSylowCenterTwo :=
  fun _ hT hcard => HeldFix.sylow_center_two hT hcard

theorem heldFourGroupGeneration : HeldFourGroupGeneration :=
  fun _ hT hcard => HeldFix.sylow_four_group_generation hT hcard

theorem heldOuterInvolutionRank : HeldOuterInvolutionRank :=
  fun _ hT hcard _ ha haP ha2 _ ha₁ ha₁2 hc =>
    HeldFix.sylow_outer_involution_rank hT hcard ha haP ha2 ha₁ ha₁2 hc

end CFSG.ComponentClassification.GrSLit
