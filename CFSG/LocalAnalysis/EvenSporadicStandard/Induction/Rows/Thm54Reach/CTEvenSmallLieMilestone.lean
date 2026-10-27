module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenSmallLie
public import CFSG.Milestones.CT_even_small_Lie_standard_frontier

public section

namespace CFSG.EvenSporadicStandard.Induction

theorem ctEvenSmallLieStatement_of_milestone
    : CTEvenSmallLieStatement :=
  fun G _ _ _ hnonab hK L hL hcore S hS htype hexc hres hbcd =>
    CFSG.Milestones.ct_even_small_lie_standard_frontier_models G hnonab hK L hL hcore S hS htype
      hexc hres hbcd

end CFSG.EvenSporadicStandard.Induction
