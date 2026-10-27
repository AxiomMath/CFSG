module

public import CFSG.ClassicalInvolution.Q3.TL4Res2FMain
public import CFSG.ClassicalInvolution.Q3.TL4D1Basic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.Ih8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem thm4RBelow_of_cit3Below {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (hE : ExitModelR n) : Thm4RBelow 3 n :=
  thm4RBelow_of_res2F' (fun _ => thm4Res2C3_of_thmD1 hP.thmD.d1)
    (thm4Res2F'_of_exitModelR (hP.twin rfl).toSet (tightBelowR_three_iff.mp hP.tbelow)
      (PhilipHall.InductionBridge.ih8T_of_cit3Below hA).thm4 hE)

end CFSG.ClassicalInvolution.Q3.TL4
