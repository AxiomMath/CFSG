module

public import CFSG.GH74.GLS.C3.Layer1.LayerITop5
public import CFSG.GH74.GLS.C3.Layer1.EvenAltConfig
public import CFSG.GH74.GLS.C3.Layer1.EvenSpor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.EvenStd

public section

namespace CFSG.GH74.GLS

theorem s_layerI_of_kgroup_leaves8_g4_thm1
    (h1 : S_stage1_rank4) (h3 : S_thm2_rank4)
    (he1 : B_even_select) (hPU4 : B_cor_PU4) (h73 : B_ivk_7_3_L2_g4)
    (hJ2 : B_spor_J2_table) (hOut : B_spor_outer_invol) (hFus : B_spor_fusion)
    (hT1 : S_thm1_rank4)
    (h81 : B_iv2_8_1) (h92 : B_lemma92) (h102 : B_ivk_10_2) (h102a : B_ivk_10_2a)
    (hL34 : B_gen4_noL34_elem) (hPGL : B_prop91_PGL) (ha : B_lemma113a) (hL27 : B_lemma113_L27)
    (hd : B_lemma113_d6) (hA : C3.Layer1.Bk.B_L114_fusion5) (hF : C3.Layer1.Bk.B_L114_final57) :
    S_layerI :=
  s_layerI_of_parts h1 hT1 h3
    (s_evenSetup_of_leaves' he1 (b_even_std_of_PU4 hPU4) (b_even_N_core_of_7_3_g4 h73) b_even_N_alt_proved
      (b_even_N_spor_of_tables hJ2 hOut hFus))
    (s_back_of_all_leaves5 h81 h92 h102 h102a hL34 hPGL ha hL27 hd hA hF)

end CFSG.GH74.GLS
