module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Final
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Final61
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Prop66b
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem65
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Final46
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Prop59
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Gen4Final
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Final

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

structure Sec6Hyps : Prop where
  hII : II4_4_4_center
  h44 : II4_44
  h31 : IVK_3_1a_lifted
  hrec : Bg.B_reciprocity
  h19l : IVK_1_9_lifted
  h12 : IVK_1_2f_lifted
  hsdfus : SD_involution_fusion
  hbal : L45_balance_step
  hIG : IG_15_16_ext
  hE : P_normal_four
  hFS : FStar_C
  h95 : III2_9_5_r2
  h52a : IVK_1_2j_52
  h52b : IVK_1_9_52
  h32l : IVK_3_2_lifted
  h32a : IVK_3_2a_strong
  hsq : IVK_f_sq
  hin : IVK_f_inner
  hco : IVK_f_coset
  hce : IVK_f_cent
  hnc : P_noncyclic
  hq2 : TwoGroup_coset_sq
  hq : II4_4_quat
  hlift : II4_ord4_lift
  hdiag : IVK_diag_unique
  h19 : IVK_1_9_outer
  hsd : SD_facts
  hsdq : SD_sq_not_z
  hqc : Quat_centr
  hrn : Rnormal4
  h119V : IVK_1_19_V
  hSR : IVK_SR_abelian
  hCR : II4_ord4_R
  hZsq : Z_not_sq
  hIA : IA_4_5_1
  hrest : Prop49_rest
  h14 : IVK_1_4a_quat
  h119 : IVK_1_19_lift
  h4hij : IVK_1_4hij_outer
  hQN : Quat_normal_index
  hQDSD : Q_DSD
  hfA : IVK_fAut_r1
  h32r1 : IVK_3_2a_r1
  hcoset : TwoGroup_coset_sq_gen
  hcyc : Lem510_cyc'
  hpow : IVK_f_pow
  htriv : IVK_triv_fAut
  hsqR : IVK_f_sq_R
  hL65 : Lem65_core
  hshape : Bg.B_two_maximalClass_shape

namespace Sec6Hyps

variable (H : Sec6Hyps)

include H

theorem prop_4_1 : Prop4_1 :=
  Sec4.prop_4_1 H.hII H.h31 H.hrec H.h19l H.h12 H.hsdfus H.hbal

theorem prop_4_6 : Prop4_6 :=
  Sec6.prop_4_6 H.hII H.h44 H.hq H.hdiag H.h19 H.hsd H.hsdq H.hqc H.hrn H.h119V H.hSR H.hCR

theorem prop_4_9 : Prop4_9 :=
  Sec6.prop_4_9 H.hII H.hq H.hdiag H.h19 H.hsd H.hsdq H.hqc H.hrn H.hZsq H.hlift H.hshape H.hIA H.hrest

theorem lemma_6_4 : Lemma6_4 := Sec6.lemma_6_4 H.prop_4_6 H.prop_4_9 H.h4hij H.htriv

theorem lemma_6_5 : Lemma6_5 := Sec6.lemma_6_5 H.prop_4_1 H.hL65

theorem prop_5_9_r1 : Prop5_9_r1 := Sec6.prop_5_9_r1 H.hIG H.hQDSD

theorem lemma_5_10_r1 : Lemma5_10_r1 :=
  Sec6.lemma_5_10_r1 H.prop_4_6 H.hfA H.hcoset H.h32r1 H.hcyc

theorem prop_5_1 : Prop5_1 :=
  Sec5.prop_5_1_gen4 H.hII H.hq H.prop_4_1 H.hIG H.hE H.h52a H.h52b H.h32l (fun _ _ _ _ _ _ _ h => h.gen4)

theorem prop_5_9 : Prop5_9 := Sec5.prop_5_9 H.hII H.hFS H.h95 H.prop_4_1

theorem lemma_5_10 : Lemma5_10 :=
  Sec5.lemma_5_10 H.hII H.prop_4_1 H.prop_5_1 H.hsq H.hin H.hco H.hce H.hnc H.hq2 H.h32a

theorem prop_6_1 : Prop6_1 :=
  Sec6.prop_6_1 H.h14 H.h119 H.htriv H.hpow H.hsqR H.hII H.prop_5_9_r1 H.lemma_5_10_r1 H.prop_5_9
    H.lemma_5_10 H.lemma_6_4 H.lemma_6_5

theorem prop_6_6 : Prop6_6 := Sec6.prop_6_6 H.hII H.hq H.hQN H.h4hij H.prop_4_1

end Sec6Hyps

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
