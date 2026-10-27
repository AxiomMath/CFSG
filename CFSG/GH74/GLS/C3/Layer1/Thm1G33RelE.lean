module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Fus
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Rel

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1G33

theorem b_thm1_L33e_rel_proved
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel) :
    B_thm1_L33e_rel := by
  intro G _ _ hG hNo x y K T V W f z hyp hnz h5
  have E := env33_of_rel h2hb h102 hL34 hP31s hP31c hL32 hG hNo hyp h5
  exact E.key_e hnz (E.fus33 h2hb hG)

end CFSG.GH74.GLS
