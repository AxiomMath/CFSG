module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbr
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Final
public import CFSG.CGT.PushingUpLit.SolKNA.R4.E3Z2Final
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TL4

section Closed


variable {r n : ℕ}

theorem tightEdgeFalseSR_of_linkZ2L2Big
    (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hZ : TightLinkZ2L2BigR r n) :
    TightEdgeFalseSR r n :=
  have hGH : GH74SectionalModels := CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models
  tightEdgeFalseSR_of_two_residuals hr hNo h4 hGH
    (tightAlphaNoNbrR_of_four_le hr hNo h4 hGH (fun m => tightLargeEdgeSR_holds hr m) hZ)
    (tightE3Z2R_of_four_le hr hNo h4 hGH fun m => tightLargeEdgeSR_holds hr m)

end Closed

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
