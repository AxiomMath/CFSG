module

public import CFSG.GH74.GLS.Stage1.Main.Final
public import CFSG.GH74.GLS.Stage1.Main.NoFAutProof
public import CFSG.GH74.GLS.Stage1.Main.BrRank7
public import CFSG.GH74.GLS.Stage1.Main.BrBase
public import CFSG.GH74.GLS.Stage1.Main.BridgeSplit
public import CFSG.GH74.GLS.Stage1.Main.RankG2Final
public import CFSG.GH74.GLS.Stage1.Main.BrFusedBase
public import CFSG.GH74.GLS.Stage1.Main.BrG2BaseThm
public import CFSG.GH74.GLS.Stage1.Main.BrG2Main
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylMain
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassW
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassY
public import CFSG.GH74.GLS.Stage1.Thm4.Lemma98
public import CFSG.GH74.GLS.Stage1.Thm4.P92Main
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.All
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1All
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229Aut
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafL76
public import CFSG.GH74.GLS.Stage12.Stage1Reduced
public import CFSG.GH74.GLS.Bg.Pu5.Final
public import CFSG.GH74.GLS.Bg.Iii2.Main
public import CFSG.GH74.GLS.Stage1.Main.L79Final
public import CFSG.GH74.GLS.Stage1.Thm4.L96C2
public import CFSG.GH74.GLS.IVK.Lifted.Alt51f
public import CFSG.GH74.GLS.IVK.Lifted.Cent4j
public import CFSG.GH74.GLS.IVK.Lifted.Dih7
public import CFSG.GH74.GLS.IVK.Lifted.SporadicNoRank1
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassC

public section

namespace CFSG.GH74.GLS.Stage12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Main CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm3.Sec8

structure Sec9Leaves : Prop

theorem Sec9Leaves.h96 (_S : Sec9Leaves) : CFSG.GH74.GLS.Stage1.Thm4.Lemma9_6 :=
  CFSG.GH74.GLS.Stage1.Thm4.lemma9_6_thm

structure Stage1Leaves : Prop where
  sec6 : Sec6Leaves
  sec9 : Sec9Leaves

namespace Stage1Leaves

variable (L : Stage1Leaves)

include L

theorem hyps
    : Sec6Hyps := L.sec6.toHyps

theorem hbase
    : BaseBridge :=
  BaseBridge.of_parts (Stage1.Main.baseBridge7_thm L.sec6.hII L.hyps.prop_4_1)
    (BaseBridgeRest.of_parts Stage1.Main.baseBridgeG2_thm Stage1.Main.baseBridgeF_thm)

theorem hL73
    : Lemma7_3 :=
  lemma_7_3 L.hyps.hII L.hyps.hq (IVK.Lifted.ivk_1_4j_lifted_of_II4 L.sec6.h44) iv2_2_5

theorem hL74
    : Lemma7_4 :=
  lemma_7_4 L.hyps.hII L.hyps.hq quat_mod_center L.hyps.prop_4_1 (ig_10_32_P L.hyps.hII)

theorem hL77
    : Lemma7_7 :=
  lemma_7_7 L.hyps.hII (Leaf.l76_struct L.sec6.hII L.hyps.hq)
    (Leaf.l77_no_conj_final L.hyps.hII (lemma_7_3 L.hyps.hII L.hyps.hq (IVK.Lifted.ivk_1_4j_lifted_of_II4 L.sec6.h44) iv2_2_5)
      L.sec6.hG327 L.hyps.prop_4_1 L.hyps.hFS)

theorem hP72
    : Prop7_2 :=
  prop_7_2_of_closed L.hyps.hII L.hyps.hq L.hyps.prop_4_1 (IVK.Lifted.ivk_1_4j_lifted_of_II4 L.sec6.h44)
    (IVK.Lifted.ivk_1_2d_lifted_of_II4 L.sec6.h44 L.sec6.hII)
    (IVK.Lifted.ivk_3_1c_lifted_of_II4 L.sec6.h44 L.sec6.hII L.hyps.hFS)
    (Leaf.l76_struct L.sec6.hII L.hyps.hq)
    (Leaf.l77_no_conj_final L.hyps.hII (lemma_7_3 L.hyps.hII L.hyps.hq (IVK.Lifted.ivk_1_4j_lifted_of_II4 L.sec6.h44) iv2_2_5)
      L.sec6.hG327 L.hyps.prop_4_1 L.hyps.hFS) (Stage1.Main.l79_thm L.hyps.hII L.hyps.h44)
    (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_5 L.hyps.hII L.hyps.h31 L.hyps.hrec L.hyps.hbal)

theorem hpsp
    : PSp4Extra :=
  Stage1.Main.psp4Extra_of_parts L.sec6.hII L.hyps.prop_4_1
    (Stage1.Main.psp4TwoClass_proved L.sec6.hII L.hyps.prop_4_1 L.hyps.prop_6_1 L.hyps.prop_6_6 L.hyps.hE
      (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_4 L.hyps.hII L.hyps.hrec L.hyps.h19l L.hyps.h12 L.hyps.hsdfus)
      (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_5 L.hyps.hII L.hyps.h31 L.hyps.hrec L.hyps.hbal)
      L.hyps.h31 L.hL73 L.hL74 L.hL77)

theorem hl4nf
    : L4NFExtra :=
  Stage1.Main.l4nfExtra_of_parts L.sec6.hII L.hyps.prop_4_1
    (Stage1.Main.l4nfRest_proved L.sec6.hII L.hyps.prop_4_1 L.hyps.prop_6_1 L.hyps.prop_6_6 L.hyps.hE
      (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_4 L.hyps.hII L.hyps.hrec L.hyps.h19l L.hyps.h12 L.hyps.hsdfus)
      (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_5 L.hyps.hII L.hyps.h31 L.hyps.hrec L.hyps.hbal)
      L.hyps.h31 L.hP72 L.hL73 L.hL74 L.hL77
      (IVK.Lifted.ivk_3_1c_lifted_of_II4 L.sec6.h44 L.sec6.hII L.hyps.hFS))

theorem hl4nfField
    : L4NFField :=
  Stage1.Main.l4nfField_proved L.sec6.hII L.hyps.prop_4_1 L.hyps.prop_6_1 L.hyps.prop_6_6 L.hyps.hE
    (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_4 L.hyps.hII L.hyps.hrec L.hyps.h19l L.hyps.h12 L.hyps.hsdfus)
    (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_5 L.hyps.hII L.hyps.h31 L.hyps.hrec L.hyps.hbal)
    L.hyps.h31 L.hP72 L.hL73 L.hL74 L.hL77
    (IVK.Lifted.ivk_3_1c_lifted_of_II4 L.sec6.h44 L.sec6.hII L.hyps.hFS)

theorem hpair7
    : PairBridge7 :=
  Stage1.Main.pairBridge7_thm L.sec6.hII L.sec6.h44 L.hyps.prop_4_1

theorem thm2
    : S_stage1_thm2_Std :=
  have h2A7 := CFSG.GH74.KGroups.TwoA7.ii4_2A7
  have hAut := IVK.Lifted.ii4_aut h2A7
  have hrec := CFSG.GH74.GLS.Stage1.Thm2.Recip.b_reciprocity_of_background
    (CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv.IG_balance_fAut_of_solv CFSG.GH74.GLS.Balance.ig_balance_fAut_solv_proved)
    L.sec6.h44 hAut L.sec6.hG327
  CFSG.GH74.GLS.Stage1.Thm2.s_stage1_thm2_Std_of_G4
    (CFSG.GH74.GLS.Bg.Pu5.b_pu5_G4_proved L.sec6.h44 IVK.Lifted.ii4_4_quat h2A7 hAut hrec)
    (CFSG.GH74.GLS.Bg.Iii2.b_iii2_G4 L.sec6.h44 hAut IVK.Lifted.ii4_4_quat)

theorem prop71
    : Prop7_1 :=
  prop_7_1_of_closed L.hyps.hII L.hyps.hq L.hyps.h44 L.hyps.prop_4_1 L.hyps.prop_6_1 L.hyps.prop_6_6
    L.hyps.hE (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_4 L.hyps.hII L.hyps.hrec L.hyps.h19l L.hyps.h12 L.hyps.hsdfus)
    (CFSG.GH74.GLS.Stage1.Thm3.Sec4.lemma_4_5 L.hyps.hII L.hyps.h31 L.hyps.hrec L.hyps.hbal)
    (IVK.Lifted.ivk_1_4j_lifted_of_II4 L.sec6.h44) (IVK.Lifted.ivk_1_2d_lifted_of_II4 L.sec6.h44 L.sec6.hII)
    (IVK.Lifted.ivk_3_1c_lifted_of_II4 L.sec6.h44 L.sec6.hII L.hyps.hFS)
    (Leaf.l76_struct L.sec6.hII L.hyps.hq)
    (Leaf.l77_no_conj_final L.hyps.hII (lemma_7_3 L.hyps.hII L.hyps.hq (IVK.Lifted.ivk_1_4j_lifted_of_II4 L.sec6.h44) iv2_2_5)
      L.sec6.hG327 L.hyps.prop_4_1 L.hyps.hFS) (Stage1.Main.l79_thm L.hyps.hII L.hyps.h44) Stage2.Final.ivk_4_10
    (IVK.Lifted.ivk_Y_unique_of_II4 L.hyps.h44 L.hyps.hII)
    Stage2.Final.ivk_4_10_supp Stage2.Final.ivk_PSp4_ne_LU

theorem prop81Rank3
    : Prop8_1Rank3 :=
  prop_8_1_rank3 L.hyps.hII L.hyps.hq L.hyps.hrec L.hyps.prop_4_1 L.hyps.prop_6_1 L.hyps.prop_6_6
    (F1.setup8_exists_thm L.hyps.hII L.hyps.hq L.hyps.h31 L.hyps.h44 CFSG.GH74.KGroups.TwoA7.ii4_2A7 L.hyps.hFS)
    L.hyps.h31 G2Syl.g2_sylow_shape
    (F1.c1_of_fused_of_swap L.hyps.hII L.hyps.h44 CFSG.GH74.KGroups.TwoA7.ii4_2A7 L.hyps.hFS)

theorem prop81
    : Prop8_1 :=
  F1.prop_8_1_of_closed_v12 L.hyps.hII L.hyps.hq L.hyps.hrec L.hyps.h44 CFSG.GH74.KGroups.TwoA7.ii4_2A7 L.hyps.prop_4_1 L.hyps.prop_6_1
    L.hyps.prop_6_6 L.hyps.h31 G2Syl.g2_sylow_shape L.sec6.hG327 L.hyps.hFS iv2_2_9_no_S3_thm

theorem prop93 : CFSG.GH74.GLS.Stage1.Thm4.Prop9_3 :=
  CFSG.GH74.GLS.Stage1.Thm4.prop_9_3 CFSG.GH74.GLS.Stage1.Thm4.lemma9_7_thm L.sec9.h96 CFSG.GH74.GLS.Stage1.Thm4.Alt51.step9_8_q1_thm (CFSG.GH74.GLS.Stage1.Thm4.step9_8_inv_of_9_6 L.sec9.h96) IVK.Lifted.ivk_5_1_index
    IVK.Lifted.ivk_5_1g IVK.Lifted.ivk_5_1f IVK.Lifted.ivk_5_1d

theorem stage1_out_four_of (hRG : RankG2)
    : Stage1OutFour :=
  Stage1.Main.stage1_out_four L.thm2 L.hyps.prop_6_1 L.prop71 L.prop81 Stage1.Thm4.prop9_2_proved L.prop93 IVK.Lifted.b2_split
    gen4NoL34_thm hRG L.hbase L.hpair7 L.hpsp L.hl4nf L.hl4nfField
    Stage1.Main.pairBridgeF_thm Stage1.Main.l4FExtra_thm Stage1.Main.noFAut_thm Stage1.Main.noFAutR1_thm IVK.Lifted.sporadic_no_rank1

theorem stage1_out_three_of (hRG : RankG2)
    : Stage1OutThree :=
  Stage1.Main.stage1_out_three_r3 L.thm2 L.hyps.prop_6_1 L.prop71 L.prop81Rank3 IVK.Lifted.b2_split gen4NoL34_thm
    Stage1.Main.rankTerm7_thm L.hbase (Stage1.Main.g2ShapeBridge_of_facts (fun Gs _ _ p f hp hp2 hf hL S' => Stage1.Thm3.Sec8.G2Syl.g2_sylow_shapeConds_fwd Gs p f hp hp2 hf hL S') hRG) Stage1.Main.noFAut_thm Stage1.Main.noFAutR1_thm

theorem stage1_out_three
    : Stage1OutThree :=
  L.stage1_out_three_of Stage1.Main.rankG2_thm

end Stage1Leaves

end CFSG.GH74.GLS.Stage12
