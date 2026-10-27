module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResC
public import CFSG.ClassicalInvolution.Q3.TL4Res2FPkg

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform

theorem thm4RTwin_of_cit3Below (hD1 : TC.Thin.D1GenLeaf 3)
    (hEM : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4Twin.Thm4TwinF.ExitModel n)
    (hER : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TL4.ExitModelR n) :
    ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n :=
  fun n hA hP =>
    Thm4Twin.thm4RTwinBelow_three_of_tight (TL4.thm4RBelow_of_cit3Below hA hP (hER n hA hP))
      (Thm4Twin.thm4TwinRes2CDTw_of_d1Gen
        (hD1 n (TC.Thin.thmDGenBelow_of_absBelow hP.thmD.d2)))
      (Thm4Twin.thm4TwinRes2F'Tw_of_exitModel (hP.twin rfl).toSet
        (tightBelowR_three_iff.mp hP.tbelow) (InductionBridge.ih8T_of_cit3Below hA).thm4
        (hEM n hA hP))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
