module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue71
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue77
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue710
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GluePure
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue72
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue74

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem lemma_7_10_of_closed (hII : II4_4_4_center) (h31c : IVK_3_1c_lifted) (h410 : IVK.IVK_4_10)
    (hY : IVK_Y_unique) (hsupp : IVK_4_10_supp) (hne : IVK_PSp4_ne_LU) :
    Lemma7_10 :=
  lemma_7_10 hII (ig_10_32_P hII) h31c h410 hY hsupp hne

theorem prop_7_2_of_closed (hII : II4_4_4_center) (hquat : II4_4_quat) (h41 : Prop4_1)
    (h14j : IVK_1_4j_lifted) (h12d : IVK_1_2d_lifted) (h31c : IVK_3_1c_lifted)
    (hL76 : L76_struct) (hL77 : L77_no_conj) (hL79 : L79_C_S_u) (hL45 : Lemma4_5) : Prop7_2 :=
  prop_7_2 hII (lemma_7_3 hII hquat h14j iv2_2_5)
    (lemma_7_4 hII hquat quat_mod_center h41 (ig_10_32_P hII)) (lemma_7_7 hII hL76 hL77)
    (lemma_7_8 hII h12d) (lemma_7_9 hII h12d h31c (ig_10_32_P hII) hL79 hL45) dih_index2_invol

theorem prop_7_1_of_closed (hII : II4_4_4_center) (hquat : II4_4_quat) (h44 : II4_44)
    (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6) (hpnf : P_normal_four) (hL44 : Lemma4_4)
    (hL45 : Lemma4_5) (h14j : IVK_1_4j_lifted) (h12d : IVK_1_2d_lifted)
    (h31c : IVK_3_1c_lifted) (hL76 : L76_struct) (hL77 : L77_no_conj) (hL79 : L79_C_S_u)
    (h410 : IVK.IVK_4_10) (hY : IVK_Y_unique) (hsupp : IVK_4_10_supp)
    (hne : IVK_PSp4_ne_LU) : Prop7_1 :=
  prop_7_1 hII h41 h61 h66 hpnf h44 hL44 hL45
    (prop_7_2_of_closed hII hquat h41 h14j h12d h31c hL76 hL77 hL79 hL45)
    (lemma_7_10_of_closed hII h31c h410 hY hsupp hne)

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
