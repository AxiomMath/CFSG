module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldCT
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius centralizerPerfectCore)

local instance e6PilotQ2FieldStep3NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Neighbour


variable {G : Type} [Group G] {L : Subgroup G} {k : Type} [Field k]

@[expose] noncomputable def q2NeighbourGE6 (e : L ≃* adjointGroup .E6 k)
    (A : Subgroup (adjointGroup .E6 k)) (N : E6Neighbour) : Subgroup G :=
  ((A.map (MulAut.conj (N.rep k)).toMonoidHom).map e.symm.toMonoidHom).map L.subtype

theorem q2NeighbourGE6_le (e : L ≃* adjointGroup .E6 k) (A : Subgroup (adjointGroup .E6 k))
    (N : E6Neighbour) : q2NeighbourGE6 e A N ≤ L :=
  map_subtype_le _

theorem q2NeighbourGE6_high (e : L ≃* adjointGroup .E6 k) (A : Subgroup (adjointGroup .E6 k)) :
    q2NeighbourGE6 e A .high = (A.map e.symm.toMonoidHom).map L.subtype := by
  have h1 : E6Neighbour.high.rep k = 1 := by
    simp [E6Neighbour.rep, E6Neighbour.word]
  have h2 : A.map (MulAut.conj (E6Neighbour.high.rep k)).toMonoidHom = A := by
    rw [h1, map_one]
    ext x
    simp
  rw [q2NeighbourGE6, h2]

theorem mem_normalizer_centralizerPerfectCore_q2NeighbourGE6 (e : L ≃* adjointGroup .E6 k)
    (A : Subgroup (adjointGroup .E6 k)) (N : E6Neighbour) {t : G}
    (ht : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer (centralizerPerfectCore (q2NeighbourGE6 e A N) : Set G) :=
  F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
    (centralizer_le_normalizer _ (centralizer_le (q2NeighbourGE6_le e A N) ht))

theorem mem_normalizer_of_eq_iSup (e : L ≃* adjointGroup .E6 k)
    (A : Subgroup (adjointGroup .E6 k)) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ N, centralizerPerfectCore (q2NeighbourGE6 e A N)) {t : G}
    (ht : t ∈ centralizer (L : Set G)) : t ∈ normalizer (G₀ : Set G) := by
  rw [hG₀]
  exact F4Pilot.mem_normalizer_iSup fun N =>
    mem_normalizer_centralizerPerfectCore_q2NeighbourGE6 e A N ht

end Neighbour

section Model


variable {k K : Type} [Field k] [Field K]

theorem baseChangeGL_mem_highRootSL2_E6 (ι : k →+* K) {x : ModGL .E6 k}
    (hx : x ∈ EPilot.highRootSL2 .E6 k) : baseChangeGL ι x ∈ EPilot.highRootSL2 .E6 K := by
  have hU : ∀ α : Fin (Tag.rank .E6) → ℤ,
      (rootSubgroup .E6 k α).map (baseChangeGL ι) ≤ rootSubgroup .E6 K α := by
    intro α
    rw [rootSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    rw [baseChangeGL_pinnedX]
    exact subset_closure ⟨ι c, rfl⟩
  have h : (EPilot.highRootSL2 .E6 k).map (baseChangeGL ι) ≤ EPilot.highRootSL2 .E6 K := by
    rw [EPilot.highRootSL2, Subgroup.map_sup]
    exact sup_le_sup (hU _) (hU _)
  exact h ⟨x, hx, rfl⟩

theorem commutator_levi_eq [Finite K] [CharP K 2] (N : E6Neighbour) :
    ⁅N.levi K, N.levi K⁆ = N.levi K := by
  have hD : ⁅a5Levi K, a5Levi K⁆ = a5Levi K := isPerfect_iff.mp isQuasisimple_a5Levi.1
  rw [← map_conj_rep_a5Levi N, ← map_commutator, hD]

theorem sup_levi_high_six_eq_top :
    E6Neighbour.high.levi K ⊔ E6Neighbour.six.levi K = ⊤ := by
  have key : ∀ (i : Fin (Tag.rank .E6)),
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {i} ≤
        E6Neighbour.high.levi K ⊔ E6Neighbour.six.levi K := by
    intro i
    by_cases hi : i = 1
    · rw [hi]
      exact (levi_le_neighbourLevi (N := .six) (J := ({1} : Finset (Fin (Tag.rank .E6))))
        (by decide)).trans le_sup_right
    · exact (levi_le_neighbourLevi (N := .high) (Finset.singleton_subset_iff.2
        (mem_nodes_high_of_ne hi))).trans le_sup_left
  rw [eq_top_iff, ← CFSG.LieType.Ree.closure_xElement_yElement, Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact key i (xElement_mem_levi_adjDatumE6 i c)
  · exact key i (yElement_mem_levi_adjDatumE6 i c)

theorem levi_le_centralizer_map_fixedFieldInclusion [Finite K] [CharP K 2] {σ : K ≃+* K}
    {A : Subgroup (adjointGroup .E6 (fixSubfield σ))} (hAJ : A ≤ posJ (fixSubfield σ))
    (N : E6Neighbour) :
    N.levi K ≤ centralizer (((A.map (MulAut.conj (N.rep (fixSubfield σ))).toMonoidHom).map
      (fixedFieldInclusion σ) : Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) := by
  rw [← centralizer_rootPair_eq_levi N]
  refine centralizer_le ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  rw [← map_conj_rep_rootSL2 N]
  refine ⟨fixedFieldInclusion σ a, ?_, Subtype.ext ?_⟩
  · rw [SetLike.mem_coe, mem_subgroupOf, coe_fixedFieldInclusion]
    exact baseChangeGL_mem_highRootSL2_E6 _ (mem_subgroupOf.1 (hAJ ha))
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_fixedFieldInclusion, map_mul, map_inv, baseChangeGL_rep]

end Model

section Step3


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {σ : K ≃+* K} {t : G}

theorem conjugate_eq_of_q2 (hw : F4Work L (fixSubfield σ) t 1) (hq : QuadraticFrobenius K σ 1)
    (e : L ≃* adjointGroup .E6 (fixSubfield σ)) {A : Subgroup (adjointGroup .E6 (fixSubfield σ))}
    (hAJ : A ≤ posJ (fixSubfield σ)) {G₀ : Subgroup G} (hperf : ⁅G₀, G₀⁆ = G₀)
    (hZ : Odd (Nat.card (center G₀))) (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K)
    (hE : ∀ N, centralizerPerfectCore (q2NeighbourGE6 e A N) ≤ G₀) {h : G}
    (htM : t ∈ normalizer (CFSG.conjugate G₀ h : Set G))
    (hML : CFSG.conjugate G₀ h ⊓ centralizer ({t} : Set G) = L) :
    CFSG.conjugate G₀ h = G₀ := by
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  set M := CFSG.conjugate G₀ h with hMdef
  have hMp : ⁅M, M⁆ = M := commutator_conjugate_eq hperf h
  have hMZ : Odd (Nat.card (center M)) := by
    rw [hMdef, card_center_conjugate]
    exact hZ
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_quotient_center_comp_fixedFieldInclusion hw.standard
    hq.card_eq hq.apply_eq hw.card_eq e hw.orderOf_eq hw.inf_eq hMp hMZ
    ((coverConjugateQuotientCenterEquiv G₀ h).symm.trans e₀) htM
  have hLM : L ≤ M := hML ▸ inf_le_left
  have hXM : ∀ N, q2NeighbourGE6 e A N ≤ M := fun N => (q2NeighbourGE6_le e A N).trans hLM
  set π := QuotientGroup.mk' (center M) with hπ
  have hXπ : ∀ N, ((q2NeighbourGE6 e A N).subgroupOf M).map π =
      ((A.map (MulAut.conj (N.rep (fixSubfield σ))).toMonoidHom).map
        (fixedFieldInclusion σ)).map Φ.toMonoidHom := by
    intro N
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨_, ⟨a, ha, rfl⟩, hma⟩ := mem_subgroupOf.1 hm
      exact ⟨fixedFieldInclusion σ a, ⟨a, ha, rfl⟩, hΦ a m hma.symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨⟨((e.symm a : L) : G), hLM (e.symm a).2⟩, mem_subgroupOf.2 ⟨_, ⟨a, ha, rfl⟩, rfl⟩,
        (hΦ a _ rfl).symm⟩
  have hcore : ∀ N, (N.levi K).map Φ.toMonoidHom ≤
      perfectCore (centralizer ((((q2NeighbourGE6 e A N).subgroupOf M).map π :
        Subgroup (M ⧸ center M)) : Set (M ⧸ center M))) := by
    intro N
    rw [hXπ N, ← F4Pilot.map_centralizer_mulEquiv, ← CFSG.Quasithin.map_perfectCore]
    exact Subgroup.map_mono (CFSG.Quasithin.le_perfectCore_of_perfect
      (levi_le_centralizer_map_fixedFieldInclusion hAJ N) (commutator_levi_eq N))
  have htop : (⨆ N, perfectCore (centralizer (((q2NeighbourGE6 e A N).subgroupOf M :
      Subgroup M) : Set M))).map π = ⊤ := by
    rw [Subgroup.map_iSup, eq_top_iff]
    have h1 : (⊤ : Subgroup (M ⧸ center M)) =
        (E6Neighbour.high.levi K ⊔ E6Neighbour.six.levi K).map Φ.toMonoidHom := by
      rw [sup_levi_high_six_eq_top, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2
        Φ.surjective]
    rw [h1, Subgroup.map_sup]
    have hN : ∀ N : E6Neighbour, (N.levi K).map Φ.toMonoidHom ≤ ⨆ N', (perfectCore (centralizer
        (((q2NeighbourGE6 e A N').subgroupOf M : Subgroup M) : Set M))).map π :=
      fun N => (hcore N).trans ((perfectCore_centralizer_map_le _).trans
        (le_iSup (fun N' => (perfectCore (centralizer
          (((q2NeighbourGE6 e A N').subgroupOf M : Subgroup M) : Set M))).map π) N))
    exact sup_le (hN .high) (hN .six)
  have hMperf : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hTop := eq_top_of_map_eq_top_of_perfect hMperf.commutator_eq_top htop
  have hgen : M ≤ ⨆ N, perfectCore (M ⊓ centralizer (q2NeighbourGE6 e A N : Set G)) := by
    intro g hg
    have hg' : (⟨g, hg⟩ : M) ∈ ⨆ N, perfectCore (centralizer
        (((q2NeighbourGE6 e A N).subgroupOf M : Subgroup M) : Set M)) := hTop ▸ mem_top _
    have h2 := mem_map_of_mem M.subtype hg'
    rw [Subgroup.map_iSup] at h2
    simp_rw [← F4Pilot.perfectCore_inf_centralizer_eq_map (hXM _)] at h2
    exact h2
  exact F4Pilot.eq_of_le_iSup_perfectCore hgen hE
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm)

end Step3

section Transport


variable {K₀ K₁ : Type} [Field K₀] [Field K₁]

theorem map_adjointGroupE6RingEquiv_posJ_le (ε : K₀ ≃+* K₁) :
    (posJ K₀).map (adjointGroupE6RingEquiv ε).toMonoidHom ≤ posJ K₁ := by
  rintro _ ⟨a, ha, rfl⟩
  rw [posJ, mem_subgroupOf]
  exact baseChangeGL_mem_highRootSL2_E6 (ε : K₀ →+* K₁) (mem_subgroupOf.1 ha)

theorem map_adjointGroupE6RingEquiv_a5Levi_le (ε : K₀ ≃+* K₁) :
    (a5Levi K₀).map (adjointGroupE6RingEquiv ε).toMonoidHom ≤ a5Levi K₁ := by
  rintro _ ⟨a, ha, rfl⟩
  rw [a5Levi, mem_subgroupOf]
  exact F4Pilot.map_rootSpan_baseChangeGL_le (ε : K₀ →+* K₁) _ ⟨_, mem_subgroupOf.1 ha, rfl⟩

theorem map_symm_adjointGroupE6RingEquiv_a5Levi (ε : K₀ ≃+* K₁) :
    (a5Levi K₁).map (adjointGroupE6RingEquiv ε).symm.toMonoidHom = a5Levi K₀ := by
  refine le_antisymm ?_ fun a ha => ?_
  · rintro _ ⟨b, hb, rfl⟩
    rw [a5Levi, mem_subgroupOf]
    exact F4Pilot.map_rootSpan_baseChangeGL_le (ε.symm : K₁ →+* K₀) _ ⟨_, mem_subgroupOf.1 hb, rfl⟩
  · refine ⟨adjointGroupE6RingEquiv ε a, map_adjointGroupE6RingEquiv_a5Levi_le ε ⟨a, ha, rfl⟩, ?_⟩
    simp

end Transport

section Reduction


@[expose] def E6TwoFieldFamilyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K), QuadraticFrobenius K σ 1 →
    ∀ (e : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t 1 →
    ∀ A : Subgroup (adjointGroup .E6 (fixSubfield σ)), A ≤ posJ (fixSubfield σ) →
      Nat.card A = 3 →
    ∀ (X : Subgroup G), X = (A.map e.symm.toMonoidHom).map L.subtype →
    ∀ (htX : t ∈ centralizer (X : Set G)) (D : Subgroup G), D = rootLeviG e →
      NeighbourOvergroupSLFieldKind
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 1 →
      ∃ φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G, IsTwoFieldFamilyE6 e φ ∧
        twoFamilySupE6 φ = ⨆ N, centralizerPerfectCore (q2NeighbourGE6 e A N)

theorem e6TwoFieldRowCTInput_of_family (hfam : E6TwoFieldFamilyInput) : E6TwoFieldRowCTInput := by
  intro G _ _ L K₀ _ _ _ e₀ t hw A₀ hAJ _ hA htX hk
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hkσ⟩ := F4Pilot.exists_quadraticFrobenius_F4 (f := 1) le_rfl
  have hq : QuadraticFrobenius K σ 1 := ⟨hK, hσ, hσc⟩
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have : Finite (fixSubfield σ) := F4Pilot.finite_of_natCard_eq_two_pow hkσ
  let := Fintype.ofFinite K₀
  let := Fintype.ofFinite (fixSubfield σ)
  have hc : Fintype.card K₀ = Fintype.card (fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hw.card_eq, hkσ]
  set ε : K₀ ≃+* fixSubfield σ := FiniteField.ringEquivOfCardEq hc with hε
  set εG := adjointGroupE6RingEquiv ε with hεG
  set e : L ≃* adjointGroup .E6 (fixSubfield σ) := e₀.trans εG with he
  set A := A₀.map εG.toMonoidHom with hAdef
  have hAJ' : A ≤ posJ (fixSubfield σ) :=
    (Subgroup.map_mono hAJ).trans (map_adjointGroupE6RingEquiv_posJ_le ε)
  have hA' : Nat.card A = 3 := by rw [hAdef, card_map_of_injective εG.injective, hA]
  have hX : (A₀.map e₀.symm.toMonoidHom).map L.subtype =
      (A.map e.symm.toMonoidHom).map L.subtype := by
    congr 1
    rw [hAdef, Subgroup.map_map]
    congr 1
    ext a
    simp [he]
  have hD : rootLeviG e₀ = rootLeviG e := by
    rw [rootLeviG, rootLeviG]
    congr 1
    rw [← map_symm_adjointGroupE6RingEquiv_a5Levi ε, Subgroup.map_map]
    rfl
  have hw' : F4Work L (fixSubfield σ) t 1 :=
    ⟨hw.standard, hw.center_eq_bot, hw.one_le, hkσ, hw.orderOf_eq, hw.inf_eq⟩
  obtain ⟨φ, hφ, hG₀⟩ := hfam G L K σ hq e t hw' A hAJ' hA' _ hX htX _ hD hk
  obtain ⟨Ψ, -⟩ := exists_mulEquiv_center_quotient_twoFamilySupE6 hφ
  have hE : ∀ N, centralizerPerfectCore (q2NeighbourGE6 e A N) ≤ twoFamilySupE6 φ :=
    fun N => hG₀ ▸ le_iSup (fun N => centralizerPerfectCore (q2NeighbourGE6 e A N)) N
  refine ⟨twoFamilySupE6 φ, K, inferInstance, by rw [hK]; norm_num, commutator_twoFamilySupE6 hφ,
    odd_card_center_twoFamilySupE6 hφ, ⟨Ψ.symm⟩,
    mem_normalizer_of_eq_iSup e A hG₀ hw.mem_centralizer, fun h htM hML => ?_⟩
  exact conjugate_eq_of_q2 hw' hq e hAJ' (commutator_twoFamilySupE6 hφ)
    (odd_card_center_twoFamilySupE6 hφ) Ψ.symm hE htM hML

end Reduction

end CFSG.SeitzReduction.E6Pilot
