module

public import CFSG.GH74.GLS.C3.Layer1.St1Main
public import CFSG.GH74.GLS.C3.Layer1.St1PumpupEq
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk103
public import CFSG.GH74.GLS.IVK.Proofs2.C3L29Rank
public import CFSG.GH74.GLS.C3.Layer1.St1P89RTop
public import CFSG.GH74.GLS.C3.Layer1.St1Thm5C
public import CFSG.GH74.GLS.C3.Layer1.St1PumpTop
public import CFSG.GH74.GLS.C3.Layer1.St1RigTop
public import CFSG.GH74.GLS.C3.Layer1.St1P14Top

public section

namespace CFSG.GH74.GLS

open CFSG.GH74.GLS.Stage1.Thm6.Glue

theorem s_stage1_rank4_of_leaves6p
    (h720 : B_ivk_7_20_h2)
    (hIV3 : ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb)
    (hIV3A7 : ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeafA7 x Kb)
    (h102 : B_ivk_10_2) (h61 : B_ivk_6_1_L29) (h41 : B_st1_prop41_h2)
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts)
    (h85 : B_iv2_8_5) (hend : B_st1_prop71_endB) : S_stage1_rank4 := by
  have hL34 : B_gen4_noL34_elem := C3.Layer1.Bk.b_gen4_noL34_elem_proof
  have h14' : B_prop14 := b_prop14_of_h1 hL34 (b_prop14_h1_of_leaves hL34 hIV3 hIV3A7)
  have hpu' : B_st1_prop51_pumpup :=
    b_st1_prop51_pumpup_of_h2 (b_st1_prop51_pumpup_h2_proved h102 h14' hL34 hG hF)
  have h47 : B_iv2_4_7 := C3.Layer1.P47.b_iv2_4_7_proved
  exact s_stage1_rank4_of_leaves
    (b_st1_thm7_of_leaves (b_ig_6_10_of_h2 b_ig_6_10_h2_proved) (b_ivk_7_20_of_h2 h720) h14'
      (IVK.Proofs2.b_ivk_10_3_of_gen4 hL34) hL34 b_inC2_L29)
    (b_st1_prop41_of_h2 h102 hL34 h41)
    (b_st1_prop51_of_leaves h102 h14' hL34 IVK.Proofs2.b_ivk_rank_add_L29 h47 hpu')
    (b_st1_thm4_of_leaves h102 hL34 h47 IVK.Proofs2.b_ivk_L29_rank IVK.Proofs2.b_ivk_rank_add_L29)
    (b_st1_thm5_of_leavesC h102 h14' hL34 IVK.Proofs2.b_ivk_rank_add_L29 h47 h61 b_st1_lemma75
      h85 hpu' hend)
    (b_st1_thm6_of_leaves b_st1_prop81
      (b_st1_prop83_of_leaves h102 h14' hL34 IVK.Proofs2.b_ivk_rank_add_L29 b_st1_pumpup_eq)
      (b_st1_prop89_of_realize
        (C3.Layer1.P89.b_prop89_realize_of_autlevel C3.Layer1.P89.b_prop89_autlevel_proved)))

end CFSG.GH74.GLS
