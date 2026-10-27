module

public import CFSG.GH74.GLS.C3.Layer1.Th2Final6
public import CFSG.GH74.GLS.C3.Layer1.Th2A7C2
public import CFSG.GH74.GLS.C3.Layer1.Th2StdPU4
public import CFSG.GH74.GLS.C3.Layer1.Th2L83
public import CFSG.GH74.GLS.C3.Layer1.BkWire
public import CFSG.GH74.GLS.C3.Layer1.Th2P812

public section

namespace CFSG.GH74.GLS

theorem s_thm2_rank4_of_leaves13
    (h102 : B_ivk_10_2) (h3b : B_thm2_A7_3b_T) (hbal : B_thm2_bal) (h84 : B_thm2_l84_syl)
    (hPU4 : B_cor_PU4) (hpt : B_thm2_pump_terminal) (hpu : B_thm2_pump_unbal)
    (hv2 : B_thm2_v2star_ss) (h72c : B_thm2_p72c) (h85 : B_thm2_p85)
    (hA7exc : B_thm2_A7_exc) (hII : B_thm2_p812_II) (hPU3 : B_thm2_PU3) : S_thm2_rank4 :=
  s_thm2_rank4_of_leaves9 h102 h3b hbal h84
    (b_thm2_terminal_standard_of_PU4 C3.Layer1.Bk.b_gen4_noL34_elem_proof h102 hPU4) hpt hpu
    b_A7_notC2 hv2 h72c
    (b_thm2_l83_of C3.Layer1.Bk.b_gen4_noL34_elem_proof
      (b_thm2_l82_of b_ig_21_10
        (b_thm2_l74_of (b_thm2_l74_A7_of (b_thm2_A7_3b_of_T h3b)))
        (b_thm2_conn_of C3.Layer1.Bk.b_gen4_noL34_elem_proof (b_thm2_A7_3b_of_T h3b)))
      IVK.Proofs2.b_ivk_6 C3.Layer1.Bk.b_ivk_10_2a_proof)
    h85 (b_thm2_p812_of hA7exc hII) hPU3

end CFSG.GH74.GLS
