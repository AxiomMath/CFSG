module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainFamily

public section

namespace CFSG.SeitzReduction.E7Pilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)


theorem e7NormalizationInput_holds : E7NormalizationInput :=
  fun _ _ _ _ _ hσ hq => normalizationProperty_leviInclusion_high hσ hq

theorem seitzExclusion_highE7_of_four_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    (h2 : E7TwoInput) : SeitzExclusion (HighExceptional .E7) :=
  seitzExclusion_highE7_of_normalization hGLS hXodd hSpor e7NormalizationInput_holds h2

end CFSG.SeitzReduction.E7Pilot
