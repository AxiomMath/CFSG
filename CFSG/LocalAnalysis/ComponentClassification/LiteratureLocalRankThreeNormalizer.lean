module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankThreeSubgroupConnectivity
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.LiteratureLocal

open CFSG.Open CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

universe u

variable {G : Type u} [Group G]

theorem mem_conjugate_iff' (H : Subgroup G) (g x : G) :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simpa [CFSG.conjugate, MulAut.conj_apply] using
    (Subgroup.mem_map_equiv (f := MulAut.conj g⁻¹) (K := H) (x := x))

theorem conjugate_one' (H : Subgroup G) : CFSG.conjugate H 1 = H := by
  ext x
  simp [mem_conjugate_iff']

theorem conjugate_conjugate' (H : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate H g) h = CFSG.conjugate H (g * h) := by
  ext x
  simp only [mem_conjugate_iff', mul_inv_rev, mul_assoc]

theorem conjugate_mono' {A B : Subgroup G} (g : G) (h : A ≤ B) :
    CFSG.conjugate A g ≤ CFSG.conjugate B g := fun x hx => by
  rw [mem_conjugate_iff'] at hx ⊢
  exact h hx

theorem conjugate_eq_of_mem_normalizer {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : CFSG.conjugate Q g = Q := by
  ext x
  rw [mem_conjugate_iff']
  exact (Subgroup.mem_normalizer_iff.mp hg x).symm

theorem card_conjugate' (A : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_mem_E3 {E : Subgroup G} (hE : E ∈ E3 G) (g : G) :
    CFSG.conjugate E g ∈ E3 G :=
  ⟨elementary_map E hE.1 _, (card_conjugate' E g).trans hE.2⟩

theorem path_conjugate {A B : Subgroup G} (h : RankThreeSubgroupPath A B) (g : G) :
    RankThreeSubgroupPath (CFSG.conjugate A g) (CFSG.conjugate B g) :=
  rankThree_path_map (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective h

@[expose] def rankThreeClass (Estar : Subgroup G) : Set (Subgroup G) :=
  {E | E ∈ E3 G ∧ RankThreeSubgroupPath E Estar}

@[expose] def rankThreeClassStabilizer (Estar : Subgroup G) : Subgroup G where
  carrier := {g | (fun E => CFSG.conjugate E g) '' rankThreeClass Estar = rankThreeClass Estar}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, conjugate_one', Set.image_id']
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    have himage : (fun E => CFSG.conjugate E (g * h)) '' rankThreeClass Estar =
        (fun E => CFSG.conjugate E h) '' ((fun E => CFSG.conjugate E g) ''
          rankThreeClass Estar) := by
      rw [Set.image_image]
      simp only [conjugate_conjugate']
    rw [himage, hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    conv_lhs => rw [← hg]
    rw [Set.image_image]
    simp only [conjugate_conjugate', mul_inv_cancel, conjugate_one', Set.image_id']

theorem mem_rankThreeClassStabilizer_iff (Estar : Subgroup G) (g : G) :
    g ∈ rankThreeClassStabilizer Estar ↔
      (fun E => CFSG.conjugate E g) '' rankThreeClass Estar = rankThreeClass Estar :=
  Iff.rfl

theorem mem_rankThreeClassStabilizer_of_mem {Estar E : Subgroup G} {g : G}
    (hE : E ∈ rankThreeClass Estar) (hEg : CFSG.conjugate E g ∈ rankThreeClass Estar) :
    g ∈ rankThreeClassStabilizer Estar := by
  rw [mem_rankThreeClassStabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨F, hF, rfl⟩
    refine ⟨conjugate_mem_E3 hF.1 g, ?_⟩
    exact rankThree_path_trans
      (path_conjugate (rankThree_path_trans hF.2 (rankThree_path_symm hE.2)) g) hEg.2
  · intro F hF
    refine ⟨CFSG.conjugate F g⁻¹, ⟨conjugate_mem_E3 hF.1 _, ?_⟩, ?_⟩
    · have hpath := path_conjugate
        (rankThree_path_trans hF.2 (rankThree_path_symm hEg.2)) g⁻¹
      rw [conjugate_conjugate', mul_inv_cancel, conjugate_one'] at hpath
      exact rankThree_path_trans hpath hE.2
    · simp only [conjugate_conjugate', inv_mul_cancel, conjugate_one']

theorem isElemAbelian_subgroupOf {A : Subgroup G} (P : Subgroup G) (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (A.subgroupOf P) := CFSG.Open.IsElemAbelian.subgroupOf hA P

variable [Finite G]

theorem path_of_le_two_subgroup {P : Subgroup G} (hP : IsPGroup 2 P) {A B : Subgroup G}
    (hA : A ∈ E3 G) (hB : B ∈ E3 G) (hAP : A ≤ P) (hBP : B ≤ P) :
    RankThreeSubgroupPath A B := by
  have hA' : IsElemAbelian 2 (A.subgroupOf P) := isElemAbelian_subgroupOf P hA.1
  have hB' : IsElemAbelian 2 (B.subgroupOf P) := isElemAbelian_subgroupOf P hB.1
  have hAcard : Nat.card (A.subgroupOf P) = 8 := (rankThree_card_subgroupOf_eq A P hAP).trans hA.2
  have hBcard : Nat.card (B.subgroupOf P) = 8 := (rankThree_card_subgroupOf_eq B P hBP).trans hB.2
  have hrank : 3 ≤ twoRank P := by
    rw [twoRank]
    exact le_csSup (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove 2 (by decide) ⊤)
      ⟨A.subgroupOf P, le_top, hA', by rw [hAcard]; norm_num⟩
  have hpath := rankThree_path_map P.subtype Subtype.val_injective
    (rank_three_elementary_subgroup_path P hP hrank _ _ hA' hAcard hB' hBcard)
  rwa [Subgroup.map_subgroupOf_eq_of_le hAP, Subgroup.map_subgroupOf_eq_of_le hBP] at hpath

theorem exists_mem_E3_le_of_three_le_pRank {Q : Subgroup G} (h : 3 ≤ CFSG.pRank 2 Q) :
    ∃ E : Subgroup G, E ≤ Q ∧ E ∈ E3 G := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide)] at h
  obtain ⟨U, hUQ, hU, hcard⟩ := pRank_witness (by decide : 1 < 2) Q
  have hUcard : 8 ≤ Nat.card U := by
    rw [hcard]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) h : 2 ^ 3 ≤ _)
  obtain ⟨E, hEU, hE⟩ := rankThree_vertex_in_elementary U hU hUcard
  exact ⟨E, hEU.trans hUQ, hE⟩

theorem exists_mem_E3_of_three_le_pRank (h : 3 ≤ CFSG.pRank 2 G) : ∃ E : Subgroup G, E ∈ E3 G := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  obtain ⟨U, -, hU, hcard⟩ := pRank_witness (by decide : 1 < 2) (⊤ : Subgroup G)
  have hUcard : 8 ≤ Nat.card U := by
    rw [hcard]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) h : 2 ^ 3 ≤ _)
  obtain ⟨E, -, hE⟩ := rankThree_vertex_in_elementary U hU hUcard
  exact ⟨E, hE⟩

theorem exists_conjugate_le_sylow {E : Subgroup G} (hE : IsPGroup 2 E) (S : Sylow 2 G) :
    ∃ g : G, CFSG.conjugate E g ≤ S := by
  obtain ⟨P, hEP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  refine ⟨g, fun x hx => ?_⟩
  rw [mem_conjugate_iff'] at hx
  have hmem : g * x * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := hg ▸ hEP hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  simpa [MulAut.smul_def, MulAut.conj_symm_apply, mul_assoc] using hmem

theorem rank_three_component_normalizer_control (hrank : 3 ≤ CFSG.pRank 2 G) (S : Sylow 2 G) :
    (∃ E : Subgroup G, E ∈ E3 G ∧ E ≤ S) ∧
    ∀ Estar : Subgroup G, Estar ∈ E3 G → Estar ≤ S →
      ((rankThreeClassStabilizer Estar : Set G) =
          {g | (fun E => CFSG.conjugate E g) '' rankThreeClass Estar = rankThreeClass Estar}) ∧
      {E | E ∈ E3 G ∧ E ≤ S} ⊆ rankThreeClass Estar ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ rankThreeClassStabilizer Estar ∧
      (∀ V : Subgroup G, V ≤ S → IsElementaryAbelian 2 V → Nat.card V = 4 →
        3 ≤ CFSG.pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) →
        Subgroup.normalizer (V : Set G) ≤ rankThreeClassStabilizer Estar) ∧
      (∀ Q : Subgroup G, Q ≤ S → 3 ≤ CFSG.pRank 2 Q →
        Subgroup.normalizer (Q : Set G) ≤ rankThreeClassStabilizer Estar) ∧
      (¬ Conn3 G → rankThreeClassStabilizer Estar < ⊤) := by
  have hS : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  refine ⟨?_, fun Estar hEstar hEstarS => ?_⟩
  · obtain ⟨E, hE⟩ := exists_mem_E3_of_three_le_pRank hrank
    obtain ⟨g, hg⟩ := exists_conjugate_le_sylow (rankThree_elementary_isPGroup E hE.1) S
    exact ⟨_, conjugate_mem_E3 hE g, hg⟩
  have hE3S : {E | E ∈ E3 G ∧ E ≤ S} ⊆ rankThreeClass Estar := fun E hE =>
    ⟨hE.1, path_of_le_two_subgroup hS hE.1 hEstar hE.2 hEstarS⟩
  have hnormalizer : ∀ Q : Subgroup G, Q ≤ S → 3 ≤ CFSG.pRank 2 Q →
      Subgroup.normalizer (Q : Set G) ≤ rankThreeClassStabilizer Estar := by
    intro Q hQS hQrank g hg
    obtain ⟨E, hEQ, hE⟩ := exists_mem_E3_le_of_three_le_pRank hQrank
    have hEg : CFSG.conjugate E g ≤ S :=
      (conjugate_mono' g hEQ).trans ((conjugate_eq_of_mem_normalizer hg).le.trans hQS)
    exact mem_rankThreeClassStabilizer_of_mem (hE3S ⟨hE, hEQ.trans hQS⟩)
      (hE3S ⟨conjugate_mem_E3 hE g, hEg⟩)
  refine ⟨rfl, hE3S, ?_, ?_, hnormalizer, ?_⟩
  · intro g hg
    exact mem_rankThreeClassStabilizer_of_mem (hE3S ⟨hEstar, hEstarS⟩)
      (hE3S ⟨conjugate_mem_E3 hEstar g,
        (conjugate_mono' g hEstarS).trans (conjugate_eq_of_mem_normalizer hg).le⟩)
  · intro V hVS hVelem hVcard hCrank g hg
    have hV : IsElemAbelian 2 V := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp
      hVelem
    obtain ⟨B, hBC, hB⟩ := exists_mem_E3_le_of_three_le_pRank hCrank
    have hU : IsElemAbelian 2 (B ⊔ V) :=
      CFSG.ProperTwoGeneratedCore.commuting_elementary_sup B V hB.1 hV
        (hBC.trans inf_le_right)
    have hUcard : 8 ≤ Nat.card (B ⊔ V : Subgroup G) :=
      hB.2 ▸ Subgroup.card_le_of_le le_sup_left
    obtain ⟨E, hVE, hEU, hE⟩ :=
      rankThree_extend_four_in_elementary (B ⊔ V) V hU hUcard le_sup_right hVcard
    have hES : E ≤ S := hEU.trans (sup_le (hBC.trans inf_le_left) hVS)
    have hEΔ : E ∈ rankThreeClass Estar := hE3S ⟨hE, hES⟩
    have hVEg : V ≤ CFSG.conjugate E g :=
      (conjugate_eq_of_mem_normalizer hg).ge.trans (conjugate_mono' g hVE)
    have hEg := conjugate_mem_E3 hE g
    have hpath : RankThreeSubgroupPath E (CFSG.conjugate E g) :=
      rankThree_path_of_common_four E _ V hE hEg hVcard hVE hVEg
    exact mem_rankThreeClassStabilizer_of_mem hEΔ
      ⟨hEg, rankThree_path_trans (rankThree_path_symm hpath) hEΔ.2⟩
  · intro hconn
    rw [lt_top_iff_ne_top]
    intro hM
    apply hconn
    have hall : ∀ F ∈ E3 G, F ∈ rankThreeClass Estar := by
      intro F hF
      obtain ⟨g, hg⟩ := exists_conjugate_le_sylow (rankThree_elementary_isPGroup F hF.1) S
      have hFg : CFSG.conjugate F g ∈ rankThreeClass Estar := hE3S ⟨conjugate_mem_E3 hF g, hg⟩
      have hginv : g⁻¹ ∈ rankThreeClassStabilizer Estar := hM ▸ Subgroup.mem_top _
      rw [mem_rankThreeClassStabilizer_iff] at hginv
      rw [← hginv]
      exact ⟨_, hFg, by simp only [conjugate_conjugate', mul_inv_cancel, conjugate_one']⟩
    exact ⟨⟨Estar, hEstar⟩, fun A B =>
      rankThree_path_trans (hall A.1 A.2).2 (rankThree_path_symm (hall B.1 B.2).2)⟩

end CFSG.ComponentClassification.LiteratureLocal
