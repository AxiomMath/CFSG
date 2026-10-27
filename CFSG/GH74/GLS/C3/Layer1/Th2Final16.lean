module

public import CFSG.GH74.GLS.C3.Layer1.Th2Final10
public import CFSG.GH74.GLS.C3.Layer1.Th2L84Syl
public import CFSG.GH74.GLS.C3.Layer1.Th2PumpUnbal
public import CFSG.GH74.GLS.C3.Layer1.St1PumpClass
public import CFSG.GH74.GLS.C3.Layer1.Th2HYTop

public section

namespace CFSG.GH74.GLS

theorem s_thm2_rank4_of_leaves19
    (h102 : B_ivk_10_2) (h3b : B_thm2_A7_3b_T) (hbal : B_thm2_bal) (h84 : B_thm2_l84_le)
    (hPU4 : B_cor_PU4)
    (hv2 : B_thm2_v2star_ss) (h72c : B_thm2_p72c) (h85 : B_thm2_p85)
    (hA7exc : B_thm2_A7_exc) (hA7 : B_thm2_p812_A7)
    (hPU3 : B_thm2_PU3) (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) :
    S_thm2_rank4 :=
  s_thm2_rank4_of_leaves13 h102 h3b hbal
    (Th2.L84Syl.b_thm2_l84_syl_of C3.Layer1.Bk.b_gen4_noL34_elem_proof h102
      (b_thm2_l82_of b_ig_21_10
        (b_thm2_l74_of (b_thm2_l74_A7_of (b_thm2_A7_3b_of_T h3b)))
        (b_thm2_conn_of C3.Layer1.Bk.b_gen4_noL34_elem_proof (b_thm2_A7_3b_of_T h3b)))
      h84)
    hPU4
    (Th2.PumpTerm.b_thm2_pump_terminal_of C3.Layer1.Bk.b_gen4_noL34_elem_proof h102)
    (b_thm2_pump_unbal_of C3.Layer1.Bk.b_gen4_noL34_elem_proof h102
      (fun _ _ _ hP hC hU hno => C3.Layer1.PumpClass.c2_u2_fm9 hGKF hE2 hP hC hU hno))
    hv2 h72c h85 hA7exc
    (b_thm2_p812_II_of' C3.Layer1.Bk.b_gen4_noL34_elem_proof
      (b_thm2_l82_of b_ig_21_10
        (b_thm2_l74_of (b_thm2_l74_A7_of (b_thm2_A7_3b_of_T h3b)))
        (b_thm2_conn_of C3.Layer1.Bk.b_gen4_noL34_elem_proof (b_thm2_A7_3b_of_T h3b)))
      b_thm2_p812_NV'_proved hA7)
    hPU3

end CFSG.GH74.GLS
