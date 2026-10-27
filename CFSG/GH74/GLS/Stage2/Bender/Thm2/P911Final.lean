module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911L913
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911End
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Alt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911LyBridge
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Two

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Signalizer

theorem prop9_11core_of_cells (h43E : Prop4_3E) (hAlt : Core911Alt) (hSpor : Core911Spor)
    (hMcLy : Core911McLy) (hTwo : Core911Two) (hL2 : Core911L2) (hL3 : Core911L3)
    (hU3 : Core911U3) (hSp4 : Core911Sp4) (hG2 : Core911G2) (hD4 : Core911D4)
    (hL4 : Core911L4) (hU4 : Core911U4) (hL5 : Core911L5) (hU5 : Core911U5)
    (hRee : Core911Ree) : Prop9_11Core :=
  prop9_11core_of_leaves
    (cf911_of_families hAlt hSpor hMcLy hTwo hL2 hL3 hU3 hSp4 hG2 hD4 hL4 hU4 hL5 hU5 hRee)
    (lemma913a_of h43E ig_5_12_thm ig_11_8_thm) (end911_of h43E) ig_5_12_thm

theorem prop9_11core_of_lie_cells
    (h43E : Prop4_3E) (hLyA : LyAllInner) (hL2 : Core911L2) (hL3 : Core911L3)
    (hU3 : Core911U3) (hSp4 : Core911Sp4) (hG2 : Core911G2) (hD4 : Core911D4)
    (hL4 : Core911L4) (hU4 : Core911U4) (hL5 : Core911L5) (hU5 : Core911U5)
    (hRee : Core911Ree) : Prop9_11Core :=
  prop9_11core_of_cells h43E core911_alt core911_spor (core911_mcly hLyA ly_invol_oddCore)
    core911_two hL2 hL3 hU3 hSp4 hG2 hD4 hL4 hU4 hL5 hU5 hRee

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
