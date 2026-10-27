module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Dict
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {K Q : Subgroup G}

theorem S5Hyp.le_normalizer_of_map (h : S5Hyp Φ K Q) [Q.Normal] {L M : Subgroup G} (hM : M ∈ Φ)
    (hle : L.map (QuotientGroup.mk' Q) ≤
      Subgroup.normalizer ((M.map (QuotientGroup.mk' Q) : Subgroup (G ⧸ Q)) : Set (G ⧸ Q))) :
    L ≤ Subgroup.normalizer (M : Set G) := fun _ hl =>
  (h.mem_normalizer_map_iff hM).mp (hle (Subgroup.mem_map_of_mem _ hl))

theorem S5Hyp.commutator_le_of_map (h : S5Hyp Φ K Q) [Q.Normal] {L M : Subgroup G} (hL : L ∈ Φ)
    (hM : M ∈ Φ)
    (hc : ⁅L.map (QuotientGroup.mk' Q), M.map (QuotientGroup.mk' Q)⁆ ≤
      oddCoreOf (L.map (QuotientGroup.mk' Q)) ⊓ oddCoreOf (M.map (QuotientGroup.mk' Q))) :
    ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M := by
  have hLM : L ≤ Subgroup.normalizer (M : Set G) := h.le_normalizer_of_map hM
    (T3.le_normalizer_of_commutator_le' (hc.trans (inf_le_right.trans (oddCoreOf_le_self _))))
  have hML : M ≤ Subgroup.normalizer (L : Set G) := h.le_normalizer_of_map hL
    (T3.le_normalizer_of_commutator_le' (by
      rw [Subgroup.commutator_comm]
      exact hc.trans (inf_le_left.trans (oddCoreOf_le_self _))))
  rw [Subgroup.commutator_le]
  intro l hl m hm
  have hcL : ⁅l, m⁆ ∈ L := by
    have h1 : m * l⁻¹ * m⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hML hm) l⁻¹).mp (L.inv_mem hl)
    have h2 : ⁅l, m⁆ = l * (m * l⁻¹ * m⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact L.mul_mem hl h1
  have hcM : ⁅l, m⁆ ∈ M := by
    have h1 : l * m * l⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hLM hl) m).mp hm
    rw [commutatorElement_def]
    exact M.mul_mem h1 (M.inv_mem hm)
  have hcb : QuotientGroup.mk' Q ⁅l, m⁆ ∈
      ⁅L.map (QuotientGroup.mk' Q), M.map (QuotientGroup.mk' Q)⁆ := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hl)
      (Subgroup.mem_map_of_mem _ hm)
  obtain ⟨hb1, hb2⟩ := Subgroup.mem_inf.mp (hc hcb)
  rw [h.oddCoreOf_map hL] at hb1
  rw [h.oddCoreOf_map hM] at hb2
  obtain ⟨x, hx, hxe⟩ := hb1
  obtain ⟨y, hy, hye⟩ := hb2
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [← h.mk_inj hL (oddCoreOf_le_self L hx) hcL hxe]
    exact hx
  · rw [← h.mk_inj hM (oddCoreOf_le_self M hy) hcM hye]
    exact hy

theorem S5Hyp.omegaOfSet_twinSet_map (h : S5Hyp Φ K Q) [Q.Normal] {M : Subgroup G}
    (hM : M ∈ aStar Φ K) :
    omegaOfSet (barFam Φ Q) (twinSet (barFam Φ Q) (M.map (QuotientGroup.mk' Q))) =
      (fun L : Subgroup G => L.map (QuotientGroup.mk' Q)) '' omegaOfSet Φ (twinSet Φ M) := by
  rw [← h.map_twinSet (T3Core.mem_of_mem_aStar h.mem hM) (h.not_aEmpty_of_mem_aStar hM),
    h.map_omegaOfSet fun _ hL => hL.1]

theorem S5Hyp.mem_vStar_iff_map (h : S5Hyp Φ K Q) [Q.Normal] {J : Subgroup G}
    (hJ : J ∈ aStar Φ K) :
    J.map (QuotientGroup.mk' Q) ∈ vStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) ↔
      J ∈ vStar Φ K := by
  have hJΦ : J ∈ Φ := T3Core.mem_of_mem_aStar h.mem hJ
  have hsub : ∀ M : Subgroup G, omegaOfSet Φ (twinSet Φ M) ⊆ Φ := fun _ _ hL => hL.1
  constructor
  · rintro ⟨-, he⟩
    rw [h.omegaOfSet_twinSet_map Relation.ReflTransGen.refl, h.omegaOfSet_twinSet_map hJ] at he
    exact ⟨hJΦ, (h.injOn_map.image_eq_image_iff (hsub K) (hsub J)).mp he⟩
  · rintro ⟨-, he⟩
    refine ⟨map_mem_quotFamily hJΦ, ?_⟩
    rw [h.omegaOfSet_twinSet_map Relation.ReflTransGen.refl, h.omegaOfSet_twinSet_map hJ, he]

theorem S5Hyp.aStar_eq_vStar (h : S5Hyp Φ K Q) [Q.Normal]
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q))) : aStar Φ K = vStar Φ K := by
  obtain ⟨⟨heq, hcomm⟩, -⟩ := hq
  ext J
  constructor
  · intro hJ
    have hJb := h.map_mem_aStar hJ
    rw [heq] at hJb
    exact (h.mem_vStar_iff_map hJ).mp hJb
  · intro hJ
    by_contra hJA
    have hJΦ : J ∈ Φ := hJ.1
    have hJb : J.map (QuotientGroup.mk' Q) ∉ vStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) := by
      rw [← heq]
      exact fun hb => hJA ((h.mem_aStar_iff hJΦ).mp hb)
    have hnbr : ∀ M ∈ twinSet Φ K, J ∈ omegaNbr Φ M := by
      intro M hM
      have hMA : M ∈ aStar Φ K := mem_aStar_of_mem_twinSet hM
      have hMb : M.map (QuotientGroup.mk' Q) ∈
          vStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) := by
        rw [← heq]
        exact h.map_mem_aStar hMA
      have hc := hcomm _ (map_mem_quotFamily hJΦ) hJb _ hMb
      have hJM : J ≤ Subgroup.normalizer (M : Set G) := h.le_normalizer_of_map hM.1
        (T3.le_normalizer_of_commutator_le' (hc.trans (inf_le_right.trans (oddCoreOf_le_self _))))
      obtain ⟨T, hT, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := J) IsPGroup.of_bot bot_le
      refine ⟨hJΦ, fun he => hJA ?_, T, mem_RSet_of_isSylow2In hJΦ hT, hT.1, hT.1.trans hJM⟩
      rw [he]
      exact hMA
    have hmem : J ∈ omegaOfSet Φ (twinSet Φ K) := ⟨hJΦ, hnbr⟩
    rw [hJ.2] at hmem
    obtain ⟨z, hz⟩ := (h.typeR.hyp.omega1 J hJΦ).1
    exact (hmem.2 J ⟨hJΦ, z, hz, hz⟩).2.1 rfl

theorem S5Hyp.commutator_le_of_quot (h : S5Hyp Φ K Q) [Q.Normal]
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q))) :
    ∀ L ∈ Φ, L ∉ vStar Φ K → ∀ M ∈ vStar Φ K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M := by
  have heqG := h.aStar_eq_vStar hq
  obtain ⟨⟨heq, hcomm⟩, -⟩ := hq
  intro L hL hLV M hMV
  rw [← heqG] at hLV hMV
  have hLb : L.map (QuotientGroup.mk' Q) ∉ vStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) := by
    rw [← heq]
    exact fun hb => hLV ((h.mem_aStar_iff hL).mp hb)
  have hMb : M.map (QuotientGroup.mk' Q) ∈ vStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) := by
    rw [← heq]
    exact h.map_mem_aStar hMV
  exact h.commutator_le_of_map hL (T3Core.mem_of_mem_aStar h.mem hMV)
    (hcomm _ (map_mem_quotFamily hL) hLb _ hMb)

theorem S5Hyp.concl₁_of_quot (h : S5Hyp Φ K Q) [Q.Normal]
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q))) :
    aStar Φ K = vStar Φ K ∧ ∀ L ∈ Φ, L ∉ vStar Φ K → ∀ M ∈ vStar Φ K,
      ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M :=
  ⟨h.aStar_eq_vStar hq, h.commutator_le_of_quot hq⟩

theorem S5Hyp.normal_omegaGen_aStar (h : S5Hyp Φ K Q) [Q.Normal]
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q))) :
    (omegaGen (aStar Φ K)).Normal := by
  have heqG := h.aStar_eq_vStar hq
  have hcomm := h.commutator_le_of_quot hq
  have hle : ∀ L ∈ Φ, L ≤ Subgroup.normalizer ((omegaGen (aStar Φ K) : Subgroup G) : Set G) := by
    intro L hL
    by_cases hLA : L ∈ aStar Φ K
    · exact (le_omegaGen hLA).trans Subgroup.le_normalizer
    · intro l hl
      have hlM : ∀ M ∈ aStar Φ K, conjSub l M = M := by
        intro M hM
        have hc := hcomm L hL (by rwa [← heqG]) M (by rwa [← heqG])
        exact mem_normalizer_iff_conjSub_eq.mp (T3.le_normalizer_of_commutator_le'
          (hc.trans (inf_le_right.trans (oddCoreOf_le_self _))) hl)
      rw [mem_normalizer_iff_conjSub_eq]
      show (⨆ M ∈ aStar Φ K, M).map (MulAut.conj l).toMonoidHom = ⨆ M ∈ aStar Φ K, M
      simp only [Subgroup.map_iSup]
      exact iSup_congr fun M => iSup_congr fun hM => hlM M hM
  have htop : (⊤ : Subgroup G) ≤
      Subgroup.normalizer ((omegaGen (aStar Φ K) : Subgroup G) : Set G) := by
    rw [← h.gen]
    exact iSup₂_le hle
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr htop)

section Restrict

theorem subgroupOf_mem_aStar_of_le (hΦ : HypOmegaGen Φ) {H : Subgroup G}
    (hA : ∀ L ∈ aStar Φ K, L ≤ H) {L : Subgroup G} (hL : L ∈ aStar Φ K) :
    L.subgroupOf H ∈ aStar (restrictFamily Φ H) (K.subgroupOf H) := by
  induction hL with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    rename_i b c
    exact ih.tail (S2.aGraphAdj_restrict hΦ (hA b hab) (hA c (hab.tail hbc)) hbc)

theorem aStar_eq_image_of_le (hΦ : HypOmegaGen Φ) {H : Subgroup G}
    (hA : ∀ L ∈ aStar Φ K, L ≤ H) :
    aStar Φ K = (fun L' : Subgroup H => L'.map H.subtype) ''
      aStar (restrictFamily Φ H) (K.subgroupOf H) := by
  ext L
  constructor
  · intro hL
    exact ⟨L.subgroupOf H, subgroupOf_mem_aStar_of_le hΦ hA hL,
      Subgroup.map_subgroupOf_eq_of_le (hA L hL)⟩
  · rintro ⟨L', hL', rfl⟩
    exact mem_aStar_of_restrict_gen hΦ (hA K Relation.ReflTransGen.refl) hL'

theorem map_omegaGen_aStar_of_le (hΦ : HypOmegaGen Φ) {H : Subgroup G}
    (hA : ∀ L ∈ aStar Φ K, L ≤ H) :
    (omegaGen (aStar (restrictFamily Φ H) (K.subgroupOf H))).map H.subtype =
      omegaGen (aStar Φ K) := by
  rw [aStar_eq_image_of_le hΦ hA]
  unfold omegaGen
  simp only [Subgroup.map_iSup, iSup_image]

theorem thm3RowsG_congr {Φ Φ' : Set (Subgroup G)} {P : Subgroup G}
    (he : restrictFamily Φ P = restrictFamily Φ' P) : Thm3RowsG Φ P ↔ Thm3RowsG Φ' P := by
  unfold Thm3RowsG Thm3RowsA Thm3RowW
  rw [he]

theorem thm3RowsG_of_restrict_le {H : Subgroup G} {P' : Subgroup H} {P : Subgroup G}
    (hP : P'.map H.subtype = P) (hr : Thm3RowsG (restrictFamily Φ H) P') : Thm3RowsG Φ P := by
  set Φ' : Set (Subgroup G) := {L | L ∈ Φ ∧ L ≤ H} with hΦ'
  have hPH : P ≤ H := by
    rw [← hP]
    exact Subgroup.map_subtype_le P'
  have h1 : restrictFamily Φ' H = restrictFamily Φ H := by
    ext L'
    constructor
    · rintro ⟨L, ⟨hL, -⟩, hLH, rfl⟩
      exact ⟨L, hL, hLH, rfl⟩
    · rintro ⟨L, hL, hLH, rfl⟩
      exact ⟨L, ⟨hL, hLH⟩, hLH, rfl⟩
  have h2 : restrictFamily Φ' P = restrictFamily Φ P := by
    ext L'
    constructor
    · rintro ⟨L, ⟨hL, -⟩, hLP, rfl⟩
      exact ⟨L, hL, hLP, rfl⟩
    · rintro ⟨L, hL, hLP, rfl⟩
      exact ⟨L, ⟨hL, hLP.trans hPH⟩, hLP, rfl⟩
  rw [← h1] at hr
  exact (thm3RowsG_congr h2).mp (S2.thm3RowsG_of_restrict (fun _ hL => hL.2) hP hr)

end Restrict

theorem S5Hyp.concl_of_restrict (h : S5Hyp Φ K Q) [Q.Normal]
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q)))
    (hX : Thm3RConclG (restrictFamily Φ (omegaGen (aStar Φ K)))
      (K.subgroupOf (omegaGen (aStar Φ K)))) :
    Thm3RConclG Φ K :=
  ⟨h.concl₁_of_quot hq, thm3RowsG_of_restrict_le
    (map_omegaGen_aStar_of_le h.typeR.hyp fun _ hL => le_omegaGen hL) hX.2⟩

theorem S5Hyp.concl_restrict_of_at (h : S5Hyp Φ K Q) [Q.Normal]
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q)))
    (hIH : Thm3RAtG (Nat.card ↥(omegaGen (aStar Φ K)))) :
    Thm3RConclG (restrictFamily Φ (omegaGen (aStar Φ K)))
      (K.subgroupOf (omegaGen (aStar Φ K))) := by
  have hXn : (omegaGen (aStar Φ K)).Normal := h.normal_omegaGen_aStar hq
  have hOX : classicalInvolutionOddCore ↥(omegaGen (aStar Φ K)) = ⊥ :=
    TL4.oddCore_eq_bot_of_normal h.odd hXn
  have hKX : K ≤ omegaGen (aStar Φ K) := le_omegaGen Relation.ReflTransGen.refl
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp h.viol
  have hJX : J ≤ omegaGen (aStar Φ K) :=
    le_omegaGen (Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩)
  exact hIH _ rfl hOX _ (h.typeR.restrict _) _ (subgroupOf_mem_restrictFamily h.mem hKX)
    (not_aEmpty_iff.mpr ⟨_, _, _, aViol_restrict_gen h.typeR.hyp hKX hJX hv⟩)

theorem S5Hyp.concl_of_at (h : S5Hyp Φ K Q) [Q.Normal]
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q)))
    (hIH : Thm3RAtG (Nat.card ↥(omegaGen (aStar Φ K)))) : Thm3RConclG Φ K :=
  h.concl_of_restrict hq (h.concl_restrict_of_at hq hIH)

theorem S5Hyp.concl_quot_of_below (h : S5Hyp Φ K Q) [Q.Normal] (hb : Thm3RBelowG (Nat.card G)) :
    Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q)) :=
  hb _ h.card_quot_lt (G ⧸ Q) rfl h.oddCore_quot _ h.typeR_quot _ (map_mem_quotFamily h.mem)
    h.not_aEmpty_quot

theorem S5Hyp.concl_of_ne_top (h : S5Hyp Φ K Q) [Q.Normal] (hb : Thm3RBelowG (Nat.card G))
    (hX : omegaGen (aStar Φ K) ≠ ⊤) : Thm3RConclG Φ K := by
  have hlt : Nat.card ↥(omegaGen (aStar Φ K)) < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group _) fun he =>
      hX ((Subgroup.card_eq_iff_eq_top _).mp he)
  exact h.concl_of_at (h.concl_quot_of_below hb) (hb _ hlt)

theorem S5Hyp.map_omegaGen_aStar (h : S5Hyp Φ K Q) [Q.Normal] :
    (omegaGen (aStar Φ K)).map (QuotientGroup.mk' Q) =
      omegaGen (aStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q))) := by
  rw [← h.map_aStar]
  unfold omegaGen
  simp only [Subgroup.map_iSup, iSup_image]

theorem S5Hyp.rows_top_of_quot (h : S5Hyp Φ K Q) [Q.Normal]
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q)))
    (hX : omegaGen (aStar Φ K) = ⊤) : Thm3RowsG (barFam Φ Q) ⊤ := by
  have htop : omegaGen (aStar (barFam Φ Q) (K.map (QuotientGroup.mk' Q))) = ⊤ := by
    rw [← h.map_omegaGen_aStar, hX]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)
  have hrows := hq.2
  rwa [htop] at hrows

@[expose] def S5RowsTop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Φ : Set (Subgroup G)) (K Q : Subgroup G) [Q.Normal],
    S5Hyp Φ K Q → omegaGen (aStar Φ K) = ⊤ → Thm3RowsG (barFam Φ Q) ⊤ → False

theorem S5Hyp.aStar_ne_top (h : S5Hyp Φ K Q) [Q.Normal] (hR : S5RowsTop)
    (hq : Thm3RConclG (barFam Φ Q) (K.map (QuotientGroup.mk' Q))) :
    omegaGen (aStar Φ K) ≠ ⊤ :=
  fun hX => hR G Φ K Q h hX (h.rows_top_of_quot hq hX)

section Step


theorem thm3RO2Lift_of_rowsTop (h : S5RowsTop) (m : ℕ) : Thm3RO2Lift m := by
  intro Y _ _ Φ K hc htw hno hQ
  have hs := s5Hyp_of_ctx hc htw hno hQ
  have hb : Thm3RBelowG (Nat.card Y) := by
    rw [hc.card]
    exact hc.ih.below
  by_cases hX : omegaGen (aStar Φ K) = ⊤
  · exact (hs.aStar_ne_top h (hs.concl_quot_of_below hb) hX).elim
  · exact hs.concl_of_ne_top hb hX

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
