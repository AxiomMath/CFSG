module

public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.GH74.GLS.C3.Layer1.Th2Tstar

public section

namespace CFSG.GH74.GLS

theorem s_thm2_rank4_of_leaves2 (h628 : B_thm2_v2ss) (h73 : B_thm2_p73) (h72c : B_thm2_p72c)
    (hI : B_thm2_caseI) (h82 : B_thm2_l82) (h83 : B_thm2_l83)
    (h84 : B_thm2_l84) (h85 : B_thm2_p85) (h812 : B_thm2_p812) (hPU3 : B_thm2_PU3)
    (hc5 : B_thm2_cent5) : S_thm2_rank4 :=
  s_thm2_rank4_of_leaves h628 h73 h72c hI
    (caseI_M_of_leaves h84 h85 h812 hPU3) h82 h83 h84 h85 h812 hPU3 hc5 tstar_of_facts

end CFSG.GH74.GLS
