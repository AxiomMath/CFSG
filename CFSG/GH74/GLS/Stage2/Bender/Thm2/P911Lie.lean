module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Final
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911L2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911L3
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911L4
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911L5
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911U3
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911U4
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911U5
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Sp4
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911G2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911D4
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Ree

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Signalizer

theorem prop9_11core_final
    (h43E : Prop4_3E) (hLyA : LyAllInner) : Prop9_11Core :=
  prop9_11core_of_lie_cells h43E hLyA core911_l2 core911_l3 core911_u3 core911_sp4 core911_g2
    core911_d4 core911_l4 core911_u4 core911_l5 core911_u5 core911_ree

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
