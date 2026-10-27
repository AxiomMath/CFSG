module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRankOneBender
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRankOneReduction
import CFSG.HardMathSupport.Malle.OvergroupTransport.Bender

public section

namespace CFSG.GroupTheory

open CFSG.HardMathSupport.Malle.OvergroupTransport

theorem gomiChevRankOneOvergroups_holds : GomiChevRankOneOvergroups :=
  gomiChevRankOneOvergroups_of_normalizerMaximal fun _ _ _ h U =>
    normalizerMaximal_of_fusionIsBenderGroup (fusionIsBenderGroup_of_isGomiRankOne h) U

end CFSG.GroupTheory
