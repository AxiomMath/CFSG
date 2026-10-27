module

public import CFSG.GH74.GLS.C3.Layer1.Th2Final5
public import CFSG.GH74.GLS.C3.Layer1.Th2V2ss

public section

namespace CFSG.GH74.GLS

theorem s_thm2_rank4_of_leaves9
    (h102 : B_ivk_10_2) (h3b : B_thm2_A7_3b_T) (hbal : B_thm2_bal) (h84 : B_thm2_l84_syl)
    (hstd : B_thm2_terminal_standard) (hpt : B_thm2_pump_terminal) (hpu : B_thm2_pump_unbal)
    (hA7 : B_A7_notC2) (hv2 : B_thm2_v2star_ss) (h72c : B_thm2_p72c) (h83 : B_thm2_l83)
    (h85 : B_thm2_p85) (h812 : B_thm2_p812) (hPU3 : B_thm2_PU3) : S_thm2_rank4 :=
  s_thm2_rank4_of_leaves8 h102 h3b hbal h84 hstd hpt hpu (b_thm2_v2ss_of hA7 hv2) h72c h83 h85
    h812 hPU3

end CFSG.GH74.GLS
