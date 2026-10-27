module

import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBLeviInput
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBHom
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBX
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBMove

public section

namespace CFSG.SeitzReduction.LinearPilot

theorem wOneOfXInput : WOneOfXInput :=
  fun _ _ _ _ _ _ hVc hV2 ht htV htnV hker hsurj hsq hcomm hL₁t hL₁V haut _ =>
    exists_wOne_of_seitzRadX hVc hV2 ht htV htnV hker hsurj hsq hcomm hL₁t hL₁V haut

theorem homocyclicExclusionInput : HomocyclicExclusionInput :=
  fun _ _ _ _ _ _ hcomm hWc hVW hVc hV2 hWV hL₁W _ haut hfaith =>
    homocyclic_exclusion hcomm hWc hVW hVc hV2 hWV hL₁W haut hfaith

theorem lFiveWOneInput_of_lFiveMovesTInput (hmove : LFiveMovesTInput) : LFiveWOneInput :=
  lFiveWOneInput_of hmove pointRadicalLeviInput wOneOfXInput homocyclicExclusionInput

theorem lFiveWOneInput_of_radical (hrad : LFiveRadicalInput) : LFiveWOneInput :=
  lFiveWOneInput_of_lFiveMovesTInput (lFiveMovesTInput_of_radical hrad)

end CFSG.SeitzReduction.LinearPilot
