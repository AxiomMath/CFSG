module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Final
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510Main
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Derived
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Main
public import CFSG.GH74.KGroups.TwoA7
public import CFSG.GH74.GLS.Stage1.Main.II4Proof
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.III295Proof
public import CFSG.GH74.GLS.Balance.Bender.Final
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.L45P1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIAMain
public import CFSG.GH74.GLS.Stage1.Main.P49Local
public import CFSG.GH74.GLS.IVK.Lifted32.Top
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Main
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Done
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Closed
public import CFSG.GH74.GLS.IVK.Lifted.Lem31a
public import CFSG.GH74.GLS.IVK.Lifted.Ord4Lift
public import CFSG.GH74.GLS.IVK.Lifted.Ord4R
public import CFSG.GH74.GLS.IVK.Lifted.QDsd
public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
public import CFSG.GH74.GLS.IVK.Lifted.SRAbelian
public import CFSG.GH74.GLS.IVK.Lifted.SqR
public import CFSG.GH74.GLS.IVK.Lifted.TwoGroups3
public import CFSG.GH74.GLS.IVK.Lifted.ZNotSq

public section

namespace CFSG.GH74.GLS.Stage12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip

structure Sec6Leaves : Prop

theorem Sec6Leaves.h44
    (_L : Sec6Leaves) : II4_44 := Stage1.Main.ii4_44_thm

theorem Sec6Leaves.hII
    (_L : Sec6Leaves) : II4_4_4_center := Stage1.Main.ii4_4_4_center_thm

theorem Sec6Leaves.hG327
    (_L : Sec6Leaves) : IG_3_27 := Stage1.Thm2.Recip.IG327F.IG_3_27_proof

theorem Sec6Leaves.toHyps
    (L : Sec6Leaves) : Sec6Hyps := by
  have h2A7 : IVK.Lifted.II4_2A7 := CFSG.GH74.KGroups.TwoA7.ii4_2A7
  have hAut : II4_Aut := IVK.Lifted.ii4_aut h2A7
  have hFS : FStar_C := IVK.Lifted.fStar_C_of_II4 L.hII
  have h31 : IVK_3_1a_lifted := IVK.Lifted.ivk_3_1a_lifted_of_II4 L.h44 hAut L.hII
  have h19l : IVK_1_9_lifted := IVK.Lifted.ivk_1_9_lifted_of_II4 L.h44 h2A7 hAut L.hII
  have hrec : Bg.B_reciprocity := b_reciprocity_of_background (Stage1.Thm2.Recip.BalanceSolv.IG_balance_fAut_of_solv CFSG.GH74.GLS.Balance.ig_balance_fAut_solv_proved) L.h44 hAut L.hG327
  have h12 : IVK_1_2f_lifted := ivk_1_2f_lifted_of_II4 L.h44 hAut
  have hsdfus : SD_involution_fusion := IVK.Lifted.sd_involution_fusion
  have hbal : L45_balance_step := CFSG.GH74.GLS.Stage1.Thm3.Sec4.l45_balance_step_thm L.hII h31 L.hG327
  have h41 : Prop4_1 := CFSG.GH74.GLS.Stage1.Thm3.Sec4.prop_4_1 L.hII h31 hrec h19l h12 hsdfus hbal
  have hL65 : Lem65_core := Stage1.Thm3.Sec6.L65.lem65_core_of_714 L.hII hrec h41 hFS
    (IVK.Lifted.ivk_1_4hij_outer_of_II4 L.h44 h2A7) IVK.Lifted.ii4_4_quat L.hG327 b_B2_g4_proved
    IVK.Proofs2.ivk_7_14_g4_closed (fun _ _ _ _ _ _ _ h => h.kgh)
  exact
    { hII := L.hII,
      h44 := L.h44,
      h31 := h31,
      hrec := hrec,
      h19l := h19l,
      h12 := h12,
      hsdfus := hsdfus,
      hbal := hbal,
      hIG := ig_15_16_ext_thm,
      hE := IVK.Lifted.p_normal_four_of_II4 L.hII,
      hFS := hFS,
      h95 := IVK.Lifted.iii2_9_5_r2_of_II4 L.h44 h2A7,
      h52a := IVK.Lifted.ivk_1_2j_52_of_II4 L.h44 h2A7 L.hII,
      h52b := IVK.Lifted.ivk_1_9_52_of_II4 L.h44 h2A7 L.hII,
      h32l := IVK.Lifted32.ivk_3_2_lifted_thm L.hII L.h44 h2A7,
      h32a := IVK.Lifted.ivk_3_2a_strong_of_II4 L.h44 h2A7,
      hsq := IVK.Lifted.ivk_f_sq_of_II4 L.h44 h2A7,
      hin := IVK.Lifted.ivk_f_inner_of_II4 L.h44 h2A7,
      hco := IVK.Lifted.ivk_f_coset_of_II4 L.h44 h2A7,
      hce := IVK.Lifted.ivk_f_cent_of_II4 L.h44 h2A7 L.hII,
      hnc := IVK.Lifted.p_noncyclic,
      hq2 := IVK.Lifted.twoGroup_coset_sq,
      hq := IVK.Lifted.ii4_4_quat,
      hlift := IVK.Lifted.ii4_ord4_lift_of_II4 L.h44 hAut,
      hdiag := IVK.Lifted.ivk_diag_unique_of_II4 L.h44 h2A7,
      h19 := IVK.Lifted.ivk_1_9_outer_of_II4 L.h44 h2A7 L.hII,
      hsd := IVK.Lifted.sd_facts,
      hsdq := IVK.Lifted.sd_sq_not_z,
      hqc := IVK.Lifted.quat_centr,
      hrn := IVK.Lifted.rnormal4 L.hII,
      h119V := IVK.Lifted.ivk_1_19_V,
      hSR := IVK.Lifted.ivk_SR_abelian_of_II4 L.h44 h2A7,
      hCR := IVK.Lifted.ii4_ord4_R_of_II4 L.hII (IVK.Lifted.ii4_ord4_lift_of_II4 L.h44 hAut),
      hZsq := IVK.Lifted.z_not_sq_of_II4 L.h44 hAut L.hII hrec,
      hIA := ia_4_5_1,
      hrest := prop49_rest_of_local L.hII IVK.Lifted.ii4_4_quat (IVK.Lifted.ivk_diag_unique_of_II4 L.h44 h2A7)
        (IVK.Lifted.ivk_1_9_outer_of_II4 L.h44 h2A7 L.hII) IVK.Lifted.sd_facts IVK.Lifted.sd_sq_not_z
        IVK.Lifted.quat_centr (IVK.Lifted.rnormal4 L.hII) L.h44
        CFSG.GH74.Uniqueness.SU.SU1.b_two_maximalClass_shape
        (CFSG.GH74.GLS.Stage1.Thm3.Sec6.prop49_local_thm L.hII IVK.Lifted.ii4_4_quat
          (IVK.Lifted.ivk_diag_unique_of_II4 L.h44 h2A7) (IVK.Lifted.ivk_1_9_outer_of_II4 L.h44 h2A7 L.hII)
          IVK.Lifted.sd_facts IVK.Lifted.sd_sq_not_z IVK.Lifted.quat_centr (IVK.Lifted.rnormal4 L.hII) L.h44
          (IVK.Lifted.ii4_ord4_lift_of_II4 L.h44 hAut) ig_15_16_ext_thm),
      h14 := IVK.Lifted.ivk_1_4a_quat,
      h119 := IVK.Lifted.ivk_1_19_lift_of_II4 L.h44 h2A7,
      h4hij := IVK.Lifted.ivk_1_4hij_outer_of_II4 L.h44 h2A7,
      hQN := IVK.Lifted.quat_normal_index,
      hQDSD := IVK.Lifted.q_dsd,
      hfA := IVK.Lifted.ivk_fAut_r1_of_II4 L.h44 h2A7 L.hII,
      h32r1 := IVK.Lifted.ivk_3_2a_r1_of_II4 L.h44 h2A7,
      hcoset := IVK.Lifted.twoGroup_coset_sq_gen,
      hcyc := CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510.lem510_cyc_weak_thm L.h44 h2A7,
      hpow := IVK.Lifted.ivk_f_pow_of_II4 L.h44 h2A7,
      htriv := IVK.Lifted.ivk_triv_fAut_of_std,
      hsqR := IVK.Lifted.ivk_f_sq_R_of_II4 L.h44 h2A7 L.hII h41,
      hL65 := hL65,
      hshape := CFSG.GH74.Uniqueness.SU.SU1.b_two_maximalClass_shape }

end CFSG.GH74.GLS.Stage12
