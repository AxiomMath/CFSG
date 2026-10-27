module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSLFour
public import CFSG.Sporadic.Bridge.Converse
public import CFSG.Open.MonsterY443Finiteness

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

section Main


theorem sporadicFixedSLFourInput : LinearPilot.SporadicFixedSLFourInput :=
  sporadicFixedSLFourInput_of_simple fun S _ _ hsp =>
    (Sporadic.Bridge.finite_simple_of_sporadicRep Open.Open.monster_y443_derived_card
      Open.Open.monster_y443_derived_simple S hsp).2

end Main

end CFSG.SeitzReduction.SporadicRefine
