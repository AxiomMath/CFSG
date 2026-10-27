module

public import CFSG.ClassicalInvolution.Q3.TL4G23Inner
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205HU33Pf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf15Supply

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

theorem g2ModelInnerOddFree_holds : G2ModelInnerOddFree :=
  fun _ _ _ _ h => TL4.autOddFreeInner_of_lieModel_g2_three h

theorem frameHyp51AG_holds_of (hG2 : G2ModelInnerOddFree) : FrameHyp51AG :=
  frameHyp51AG_of_models TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert
    TwinCentRes.modelFactM12_of_certs TwinThmEW.t4Supply_of_twoClass frameOuterFixedOddFree_PSU3
    (CFSG.Sporadic.Mathieu.fam_m12_simplicity).1 m12_nonabelian hG2

theorem frameHyp51AzG_holds_of (hG2 : G2ModelInnerOddFree) : FrameHyp51AzG :=
  frameHyp51AzG_of_models TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert
    TwinCentRes.modelFactM12_of_certs TwinThmEW.t4Supply_of_twoClass frameOuterFixedOddFree_PSU3
    (CFSG.Sporadic.Mathieu.fam_m12_simplicity).1 m12_nonabelian hG2

theorem frameHyp51BG_holds_of (hG2 : G2ModelInnerOddFree) : FrameHyp51BG :=
  frameHyp51BG_of_vertices (frameHyp51AG_holds_of hG2) (frameHyp51AzG_holds_of hG2)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
