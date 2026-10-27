module

public import CFSG.GH74.GLS.C3.Layer1.Th2Final
public import CFSG.GH74.GLS.C3.Layer1.Th2ConnMain
public import CFSG.GH74.GLS.C3.Layer1.Th2L84

public section

namespace CFSG.GH74.GLS

theorem s_thm2_rank4_of_leaves4 (hL34 : B_gen4_noL34_elem)
    (h3b : B_thm2_A7_3b) (h628 : B_thm2_v2ss) (h73 : B_thm2_p73) (h72c : B_thm2_p72c)
    (hI : B_thm2_caseI) (h83 : B_thm2_l83) (h84 : B_thm2_l84) (h85 : B_thm2_p85)
    (h812 : B_thm2_p812) (hPU3 : B_thm2_PU3) (hc5 : B_thm2_cent5) : S_thm2_rank4 :=
  s_thm2_rank4_of_leaves3 h628 h73 h72c (b_thm2_l74_A7_of h3b) (b_thm2_conn_of hL34 h3b) hI h83
    h84 h85 h812 hPU3 hc5

theorem s_thm2_rank4_of_leaves5 (hL34 : B_gen4_noL34_elem)
    (h3b : B_thm2_A7_3b) (h84 : B_thm2_l84_syl) (h628 : B_thm2_v2ss) (h73 : B_thm2_p73)
    (h72c : B_thm2_p72c) (hI : B_thm2_caseI) (h83 : B_thm2_l83) (h85 : B_thm2_p85)
    (h812 : B_thm2_p812) (hPU3 : B_thm2_PU3) (hc5 : B_thm2_cent5) : S_thm2_rank4 :=
  s_thm2_rank4_of_leaves4 hL34 h3b h628 h73 h72c hI h83
    (b_thm2_l84_of hL34
      (b_thm2_l82_of b_ig_21_10 (b_thm2_l74_of (b_thm2_l74_A7_of h3b)) (b_thm2_conn_of hL34 h3b))
      h84) h85 h812 hPU3 hc5

end CFSG.GH74.GLS
