module

public import CFSG.GH74.GLS.C3.Layer1.Th2Final2
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump

public section

namespace CFSG.GH74.GLS

theorem s_thm2_rank4_of_leaves7 (hL34 : B_gen4_noL34_elem)
    (h102 : B_ivk_10_2) (h103 : B_ivk_10_3) (h3b : B_thm2_A7_3b) (h84 : B_thm2_l84_syl)
    (hstd : B_thm2_terminal_standard) (hpt : B_thm2_pump_terminal) (hpu : B_thm2_pump_unbal)
    (h628 : B_thm2_v2ss) (h73 : B_thm2_p73) (h72c : B_thm2_p72c) (h83 : B_thm2_l83)
    (h85 : B_thm2_p85) (h812 : B_thm2_p812) (hPU3 : B_thm2_PU3) : S_thm2_rank4 :=
  s_thm2_rank4_of_leaves5 hL34 h3b h84 h628 h73 h72c (b_thm2_caseI_of hstd h102 hL34) h83 h85
    h812 hPU3 (b_thm2_cent5_of_pump_v2 (b_thm2_pump_v2_of hL34 h102 h103 hpt hpu))

end CFSG.GH74.GLS
