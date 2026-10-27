module

public import CFSG.GH74.GLS.C3.Layer1.Th2Final4
public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk103

public section

namespace CFSG.GH74.GLS

theorem s_thm2_rank4_of_leaves8
    (h102 : B_ivk_10_2) (h3b : B_thm2_A7_3b_T) (hbal : B_thm2_bal) (h84 : B_thm2_l84_syl)
    (hstd : B_thm2_terminal_standard) (hpt : B_thm2_pump_terminal) (hpu : B_thm2_pump_unbal)
    (h628 : B_thm2_v2ss) (h72c : B_thm2_p72c) (h83 : B_thm2_l83) (h85 : B_thm2_p85)
    (h812 : B_thm2_p812) (hPU3 : B_thm2_PU3) : S_thm2_rank4 :=
  s_thm2_rank4_of_leaves7 C3.Layer1.Bk.b_gen4_noL34_elem_proof h102
    (IVK.Proofs2.b_ivk_10_3_of_gen4 C3.Layer1.Bk.b_gen4_noL34_elem_proof)
    (b_thm2_A7_3b_of_T h3b) h84 hstd hpt hpu h628
    (b_thm2_p73_of C3.Layer1.Bk.b_gen4_noL34_elem_proof h102 h3b hbal) h72c h83 h85 h812 hPU3

end CFSG.GH74.GLS
