module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26D02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26B01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY

theorem pureBCase_of_singleFrame (hV : LayerFrattiniFact) (hSF : SingleFrameFact) :
    PureBCase := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne huni hα
  exfalso
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  exact false_of_singleFrame hV hs hdisc hμ hne huni hα F
    (hSF G Ω K J S R T W z t hs hdisc hμ hne huni hα F)
end T8YY
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
