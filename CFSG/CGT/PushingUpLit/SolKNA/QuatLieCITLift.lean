module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLift
public import CFSG.ClassicalInvolution.Q3.TL3CentTwin
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic

theorem not_tightInO2_of_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : t ≠ 1) : ¬ TightInO2 t := by
  rintro ⟨P, hPn, hP2, htP⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with rfl | rfl
  · exact ht (Subgroup.mem_bot.mp htP)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hG : IsPGroup 2 G := hP2.of_equiv Subgroup.topEquiv
    have : Nontrivial G := ⟨⟨t, 1, ht⟩⟩
    have hZ := hG.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h] at hZ
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hZ
      rw [Subgroup.mem_bot] at hx hy
      exact hxy (by simp [hx, hy])
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm

theorem tightLiftSimple_of_inductive (hC : CIT3Inductive) (hI : ∀ N, TightInductive N)
    (hE : ∀ n, TightLargeEdgeS n) (hR4 : TightR4) : TightLiftSimple := by
  intro G _ _ _ hnab hnG R S t hd
  obtain ⟨e⟩ := Q3T.MFS.nonempty_genFittingFStar_equiv G hnab
  obtain ⟨hsF, hnabF⟩ := Q3T.MFS.genFittingFStar_simple G hnab
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have hnF : ¬ TwoSubgroupsFourGenerated (genFittingFStar G) := fun hF =>
    hnG (twoSubgroupsFourGenerated_of_mulEquiv e hF)
  have hB : ∀ n, CIT3Below n := fun n Y _ _ _ Λ hΛ => hC Y Λ hΛ
  have hq8 := hR4 (Nat.card G + 1) (hB _) G (Nat.lt_succ_self _) hnabF hnF R S t hd
  have ht1 : t ≠ 1 := by
    intro h
    have := hd.order
    rw [h, orderOf_one] at this
    norm_num at this
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order]; norm_num)
  have htK : t ∈ tightCore R := Subgroup.subset_closure ⟨hd.mem_right, ht2⟩
  have hK0ne : tightCore R ≠ ⊥ := fun h => ht1 (by rw [h, Subgroup.mem_bot] at htK; exact htK)
  obtain ⟨hCF, hO⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hnabF
  have hcl : subnormalClosure (tightCore R) = ⊤ := by
    have hFle := le_subnormalClosure_of_isComponentOf
      (isComponentOf_top_of_normal_simple (genFittingFStar G) hnabF) hCF hK0ne
    rw [CFSG.ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
      hnab] at hFle
    exact eq_top_iff.mpr hFle
  have hcls : TightCls G R S t := ⟨hq8, iSup_conjSub_eq_top_of_subnormalClosure hcl, hO⟩
  have hE2 : ¬ TightInO2 t := not_tightInO2_of_simple hnab ht1
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact (hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm).elim
  have hb : TightBelow (Nat.card G) := fun Y _ _ hlt R' S' t' hd' hc' =>
    hI (Nat.card G) (hB _) Y hlt R' S' t' hd' hc'
  have hedge := hE (Nat.card G) (hB _) hb G rfl hnabF R S t hd hcls hE2 hnF
  rcases hI (Nat.card G + 1) (hB _) G (Nat.lt_succ_self _) R S t hd hcls with
    (hex | ⟨hedgeless, -⟩ | ⟨hedgeless, -⟩ | h4) | hgood
  · exact absurd hex hE2
  · exact absurd hedgeless hedge
  · exact absurd hedgeless hedge
  · exact absurd h4 (hd.not_tightE4 hcls hE2 hZ)
  · exact tightHasLift_of_good hd hgood

theorem tightLiftSimple_of_leaves₂ (hC : CIT3Inductive)
    (hF1 : TightF1S fun m => CIT3Below m ∧ TightBelow m)
    (hEnd : TightEndGameOdd fun m => CIT3Below m ∧ TightBelow m)
    (htw : ∀ n, TightTwistAllTwin n) (hsmall : TightSmallBase)
    (hliftS : ∀ n, TightLargeLiftS n) (hliftC : ∀ n, TightCentTwinLift n)
    (hR4 : TightR4) : TightLiftSimple := by
  have h11b :=
    tightC19_11bS_of_F1_endgame hF1 (tightEndGameS_of_solv (tightEndGameSolv_of_odd hEnd))
  have hE := tightLargeEdgeS_of_core h11b
  exact tightLiftSimple_of_inductive hC
    (tightInductive_of_step (tightStep_of_parts₅ htw hsmall hE hliftS hliftC)) hE hR4

end CFSG.CGT.PushingUpLit.SolKNA
