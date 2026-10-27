module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenResidual
public import CFSG.Milestones.CT_even_standard_residual_reduction

public section

namespace CFSG.EvenSporadicStandard.Induction

theorem ctEvenResidualStatement_of_milestone :
    CTEvenResidualStatement :=
  fun G _ _ _ hnonab hK L hL hcore S hS htype hexc =>
    CFSG.Milestones.ct_even_standard_residual_reduction G hnonab hK L hL hcore S hS htype hexc

end CFSG.EvenSporadicStandard.Induction
