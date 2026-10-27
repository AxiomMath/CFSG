module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3C4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D


theorem frameC204 : FrameC204 := by
  intro G _ _ _ K K' J S R R' W V z t d
  have hH := hexAllF G K K' J S R R' W V z t d
  refine d.concl20_4_of_98 hH ?_ (d.late_tor hH.JW hH.hW)
  exact (d.late_98 hH.JW hH.hW (X := centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (S.isPGroup'.to_le (fun x hx => hx.1)) (fun x hx => hx.1) (fun x hx => d.cent_comm_t hx)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer hx))).2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
