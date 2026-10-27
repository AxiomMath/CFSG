module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MainE
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneToralThm
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Thm
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L2Final
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L4Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L5Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Ly
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ReeMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporTop
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U5Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SMain

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem cf67NonAltJ1_thm
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hA : LyAllInner) (hB : LyCentralizerCore) (hC : LyMultTrivial)
    : CF67NonAltJ1 :=
cf67NonAltJ1_of_families cf67Spor_thm (cf67McLy_thm (cf67Ly_of_atlas hA hB hC)) cf67Two_thm
   (cf67L2_thm hGA) (cf67L3_thm hGA) (cf67U3_thm hGA) (cf67Sp4_thm hGA) cf67G2_thm
   (cf67D4_thm_of_a2Minus_thm g2d4InnerPlaneGen_thm) (cf67L4_thm hGA) (cf67U4_thm hGA)
   (cf67L5_thm hGA) (cf67U5_thm hGA) cf67Ree_thm

end CFSG.GH74.GLS.Stage2.Bender.Thm1
