module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.All
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx39
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx49
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx59
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx61
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx62

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem prop_8_1_of_closed_v7 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6) (hset : Setup8_exists) (h31 : IVK_3_1a_lifted)
    (hSyl : G2_Sylow_shape) (hC1 : C1_of_Fused) (h327 : IG_3_27) (hF : FStar_C)
    (h29 : IV2_2_9_no_S3) (hfin : Final81b) : Prop8_1 :=
  prop_8_1_of_closed hII hq hrec h41 h61 h66 hset h31 hSyl hC1
    (lemma_8_6 hII hq hrec (lemma_8_5_of_closed hII hq hrec h31 h41 h327 hF) h29) y34_E
    (lemma_8_9 hII hq hrec h31) (lemma_8_10 hII hq hrec)
    (final81_of_a_b (final81a hII hq hrec h31) hfin)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
