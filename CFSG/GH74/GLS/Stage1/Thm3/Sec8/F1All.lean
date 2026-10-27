module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.AllV7
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1Setup
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1C1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1Final

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem prop_8_1_of_closed_v12 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (h31 : IVK_3_1a_lifted) (hSyl : G2_Sylow_shape) (h327 : IG_3_27)
    (hF : FStar_C) (h29 : IV2_2_9_no_S3) : Prop8_1 :=
  prop_8_1_of_closed_v7 hII hq hrec h41 h61 h66 (setup8_exists_thm hII hq h31 h44 h2A7 hF) h31
    hSyl (c1_of_fused_of_swap hII h44 h2A7 hF) h327 hF h29 (final81b_thm hII hq hrec h44)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1
