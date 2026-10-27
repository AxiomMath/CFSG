module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelTop

public section

namespace CFSG.GH74.GLS

theorem s_thm1_rank4_of_base_rel
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hS34 : C3.Layer1.P34.S_prop34)
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL29 : B_inC2_L29) (hC2 : C3.Layer1.PumpCalc.C2Facts)
    (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel) (h33c : B_thm1_L33c'_rel)
    (h33d : B_thm1_L33d_rel) (h33e : B_thm1_L33e_rel) (h33f : B_thm1_L33f_rel)
    (h35 : B_thm1_L35_rel) (hcore : B_thm1_L39core_rel) (hV0 : B_thm1_L310_V0_rel) : S_thm1_rank4 :=
  s_thm1_rank4_of_rel h102 hL34
    (s_thm1_of_base_rel h102 hL34 hS34 h610 h720 h14 h103 hL29 hC2 hP31c hL32 h33c h33d h33e h33f h35
    hcore hV0)

theorem b_thm1_four_of_base_rel
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hS34 : C3.Layer1.P34.S_prop34)
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL29 : B_inC2_L29) (hC2 : C3.Layer1.PumpCalc.C2Facts)
    (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel) (h33c : B_thm1_L33c'_rel)
    (h33d : B_thm1_L33d_rel) (h33e : B_thm1_L33e_rel) (h33f : B_thm1_L33f_rel)
    (h35 : B_thm1_L35_rel) (hcore : B_thm1_L39core_rel) (hV0 : B_thm1_L310_V0_rel)
    (hfm : Th2.L625.ClassFM9) : B_thm1_four :=
  b_thm1_four_of_rel h102 hL34 hfm
    (s_thm1_of_base_rel h102 hL34 hS34 h610 h720 h14 h103 hL29 hC2 hP31c hL32 h33c h33d h33e h33f h35
    hcore hV0)

end CFSG.GH74.GLS
