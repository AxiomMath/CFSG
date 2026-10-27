module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Transfer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Graph
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Fix

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fixSubgroup_eq_map_of_inf_eq {L M : Subgroup G} (hZ : Odd (Nat.card (center M)))
    {X : Type*} [Group X] (eM : M ⧸ center M ≃* X) {t : G} (ht : orderOf t = 2)
    (htM : t ∈ normalizer (M : Set G)) (hML : M ⊓ centralizer ({t} : Set G) = L) :
    E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) =
      (L.subgroupOf M).map (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) := by
  rw [← E6Pilot.map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM]
  congr 1
  ext x
  rw [mem_subgroupOf, mem_subgroupOf, ← hML]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

omit [Finite G] in
theorem map_coverConjugateQuotientCenterEquiv_symm {L G₀ : Subgroup G} (g : G) :
    ((L.subgroupOf (CFSG.conjugate G₀ g⁻¹)).map
        (QuotientGroup.mk' (center (CFSG.conjugate G₀ g⁻¹)))).map
      (E6Pilot.coverConjugateQuotientCenterEquiv G₀ g⁻¹).symm.toMonoidHom =
    ((L.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf G₀).map
      (QuotientGroup.mk' (center G₀)) := by
  set χ := E6Pilot.coverConjugateQuotientCenterEquiv G₀ g⁻¹ with hχ
  have hχmk : ∀ x : G₀, χ (QuotientGroup.mk' (center G₀) x) =
      QuotientGroup.mk' (center (CFSG.conjugate G₀ g⁻¹)) (E6Pilot.coverConjugateEquiv G₀ g⁻¹ x) :=
    fun x => QuotientGroup.congr_mk' _ _ _ _ x
  have hcc : ∀ x : G₀, ((E6Pilot.coverConjugateEquiv G₀ g⁻¹ x : CFSG.conjugate G₀ g⁻¹) : G) =
      g * x * g⁻¹ := by
    intro x
    change (MulAut.conj g⁻¹⁻¹) (x : G) = _
    rw [inv_inv, MulAut.conj_apply]
  ext q
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (E6Pilot.coverConjugateEquiv G₀ g⁻¹).surjective y
    refine ⟨x, ?_, ?_⟩
    · simp only [SetLike.mem_coe, mem_subgroupOf] at hy ⊢
      rw [hcc] at hy
      exact ⟨g * x * g⁻¹, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    · change QuotientGroup.mk' _ x = χ.symm (QuotientGroup.mk' _ _)
      rw [← hχmk, MulEquiv.symm_apply_apply]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨QuotientGroup.mk' _ (E6Pilot.coverConjugateEquiv G₀ g⁻¹ x),
      ⟨E6Pilot.coverConjugateEquiv G₀ g⁻¹ x, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf, hcc]
      obtain ⟨l, hl, hlx⟩ := mem_subgroupOf.1 hx
      rw [← hlx]
      have : g * ((MulAut.conj g⁻¹).toMonoidHom l) * g⁻¹ = l := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rw [this]
      exact hl
    · change χ.symm (QuotientGroup.mk' _ _) = QuotientGroup.mk' _ x
      rw [← hχmk, MulEquiv.symm_apply_apply]

end Fix

section General


theorem unique_of_eta_of_conjugates {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type}
    [Field K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {t : G} (ht : orderOf t = 2) (hZ : Odd (Nat.card (center (pieceSpan e)))) {X : Type*}
    [Group X] (e₀ : pieceSpan e ⧸ center (pieceSpan e) ≃* X) (η : MulAut X)
    (htN : t ∈ normalizer (pieceSpan e : Set G))
    (h₀ : pieceSpan e ⊓ centralizer ({t} : Set G) = L ∧
      ∃ φ : MulAut X, φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = η)
    (hM : ∀ (g : G) (htM : t ∈ normalizer (CFSG.conjugate (pieceSpan e) g⁻¹ : Set G)),
      CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G) = L ∧
        ∃ φ : MulAut X, φ * normalizerQuotMulAut
          ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹).symm.trans e₀)
            ⟨t, htM⟩ * φ⁻¹ = η) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (pieceSpan e : Set G) →
      g ∈ normalizer (pieceSpan e : Set G) := by
  intro g hg
  have htM := mem_normalizer_conjugate_inv hg
  obtain ⟨hC₀, φ₀, hφ₀⟩ := h₀
  obtain ⟨hCM, φM, hφM⟩ := hM g htM
  set χ := E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹ with hχ
  set eM := χ.symm.trans e₀ with heM
  have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  have hfix₀ := fixSubgroup_eq_map_of_inf_eq hZ e₀ ht htN hC₀
  have hfixM := fixSubgroup_eq_map_of_inf_eq hZM eM ht htM hCM
  have hmap₀ := map_eqLocus_eq_of_conj hφ₀
  have hmapM := map_eqLocus_eq_of_conj hφM
  set ψ : MulAut (pieceSpan e ⧸ center (pieceSpan e)) :=
    ((e₀.trans φ₀).trans φM.symm).trans e₀.symm with hψ
  have hLM : L ≤ CFSG.conjugate (pieceSpan e) g⁻¹ := by
    intro x hx
    have h1 : x ∈ CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G) := by
      rw [hCM]
      exact hx
    exact h1.1
  have hgL : L.map (MulAut.conj g⁻¹).toMonoidHom ≤ pieceSpan e := by
    rintro _ ⟨l, hl, rfl⟩
    have h1 := hLM hl
    rw [mem_conjugate_iff_of_mul] at h1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  refine mem_normalizer_of_quotAut_map_eq hf hK e hgL ψ ?_
  rw [← map_coverConjugateQuotientCenterEquiv_symm g]
  apply Subgroup.map_injective (f := e₀.toMonoidHom) e₀.injective
  have hmap₀' : (E6Pilot.fixSubgroup (normalizerQuotMulAut e₀ ⟨t, htN⟩)).map φ₀.toMonoidHom =
      E6Pilot.fixSubgroup η := hmap₀
  have hφM' : (E6Pilot.fixSubgroup η).map φM.symm.toMonoidHom =
      E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
    change (η.toMonoidHom.eqLocus (MonoidHom.id X)).map φM.symm.toMonoidHom = _
    rw [← hmapM, Subgroup.map_map]
    have : φM.symm.toMonoidHom.comp φM.toMonoidHom = MonoidHom.id X :=
      MonoidHom.ext fun x => φM.symm_apply_apply x
    rw [this, Subgroup.map_id]
    rfl
  have hL1 : (((L.subgroupOf (pieceSpan e)).map (QuotientGroup.mk' (center (pieceSpan e)))).map
        ψ.toMonoidHom).map e₀.toMonoidHom =
      (((L.subgroupOf (pieceSpan e)).map
        (e₀.toMonoidHom.comp (QuotientGroup.mk' (center (pieceSpan e))))).map
          φ₀.toMonoidHom).map φM.symm.toMonoidHom := by
    simp only [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψ, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply]
  have hR1 : (((L.subgroupOf (CFSG.conjugate (pieceSpan e) g⁻¹)).map
        (QuotientGroup.mk' (center (CFSG.conjugate (pieceSpan e) g⁻¹)))).map
          χ.symm.toMonoidHom).map e₀.toMonoidHom =
      (L.subgroupOf (CFSG.conjugate (pieceSpan e) g⁻¹)).map
        (eM.toMonoidHom.comp (QuotientGroup.mk' (center (CFSG.conjugate (pieceSpan e) g⁻¹)))) := by
    simp only [Subgroup.map_map]
    rfl
  rw [hL1, hR1, ← hfixM, ← hfix₀, hmap₀', hφM']

end General

section Aux

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizerQuotMulAut_conjugate {G₀ : Subgroup G} {X : Type*} [Group X]
    (e₀ : G₀ ⧸ center G₀ ≃* X) {g t : G} (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G))
    (htM : t ∈ normalizer (CFSG.conjugate G₀ g⁻¹ : Set G)) :
    normalizerQuotMulAut ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ g⁻¹).symm.trans e₀)
        ⟨t, htM⟩ = normalizerQuotMulAut e₀ ⟨g⁻¹ * t * g, hg⟩ := by
  set χ := E6Pilot.coverConjugateQuotientCenterEquiv G₀ g⁻¹ with hχ
  have hχmk : ∀ x : G₀, χ (QuotientGroup.mk' (center G₀) x) =
      QuotientGroup.mk' (center (CFSG.conjugate G₀ g⁻¹)) (E6Pilot.coverConjugateEquiv G₀ g⁻¹ x) :=
    fun x => QuotientGroup.congr_mk' _ _ _ _ x
  have hcc : ∀ x : G₀, ((E6Pilot.coverConjugateEquiv G₀ g⁻¹ x : CFSG.conjugate G₀ g⁻¹) : G) =
      g * x * g⁻¹ := by
    intro x
    change (MulAut.conj g⁻¹⁻¹) (x : G) = _
    rw [inv_inv, MulAut.conj_apply]
  apply MulEquiv.ext
  intro x
  obtain ⟨q, rfl⟩ := e₀.surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center G₀) q
  have h1 : e₀ (QuotientGroup.mk' (center G₀) y) = (χ.symm.trans e₀)
      (QuotientGroup.mk' _ (E6Pilot.coverConjugateEquiv G₀ g⁻¹ y)) := by
    rw [MulEquiv.trans_apply, ← hχmk, MulEquiv.symm_apply_apply]
  rw [h1, normalizerQuotMulAut_apply, ← h1, normalizerQuotMulAut_apply, MulEquiv.trans_apply]
  congr 1
  rw [MulEquiv.symm_apply_eq, hχmk]
  congr 1
  apply Subtype.ext
  rw [hcc, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.normalizerMonoidHom_apply_apply_coe,
    hcc]
  group

omit [Finite G] in
theorem odd_card_center_of_odd_card_centralizer {G₀ : Subgroup G}
    (h : Odd (Nat.card (centralizer (G₀ : Set G)))) : Odd (Nat.card (center G₀)) := by
  refine Odd.of_dvd_nat h ?_
  rw [← Subgroup.card_map_of_injective G₀.subtype_injective]
  refine Subgroup.card_dvd_of_le ?_
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val ((mem_center_iff.1 hz) ⟨x, hx⟩)


theorem not_mem_centralizer_of_two_pow_dvd_quot {L : Subgroup G} (hset : StandardSetting G L)
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .F4 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {G₀ : Subgroup G} (hG₀ : ⁅G₀, G₀⁆ = G₀) {X : Type*} [Group X] (e₀ : G₀ ⧸ center G₀ ≃* X)
    (h2 : 2 ^ (36 * f) ∣ Nat.card X) : t ∉ centralizer (G₀ : Set G) := by
  intro htG
  have : Finite K := finite_of_natCard_eq_two_pow hK
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  have hle : G₀ ≤ L := std_perfect_le hset hOut htC ht hG₀ fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htG x hx)
  have h1 : Nat.card X ∣ Nat.card L := by
    rw [← Nat.card_congr e₀.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hle)
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK] at h1
  obtain ⟨r, hr, hrr⟩ := (EvenExc.profile_ordF4' hf).two
  rw [hrr] at h1
  have h3 : 2 ^ (f * 24) * 2 ∣ 2 ^ (f * 24) * r :=
    (by rw [← pow_succ]; exact pow_dvd_pow 2 (by omega) : 2 ^ (f * 24) * 2 ∣ 2 ^ (36 * f)).trans
      (h2.trans h1)
  have h4 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h3
  exact (Nat.not_even_iff_odd.2 hr) (even_iff_two_dvd.2 h4)

end Aux

section Inputs


@[expose] def E6RowXiExclusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f → E6RowKinds e t f →
    ∀ (K' : Type) [Field K'] [Finite K'], Nat.card K' = 2 ^ f →
      Nonempty (pieceSpan e ⧸ center (pieceSpan e) ≃* adjointGroup Tag.E6 K') →
      ∀ M : Subgroup G, (∃ g : G, M = CFSG.conjugate (pieceSpan e) g) →
      ∀ (htM : t ∈ normalizer (M : Set G))
        (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K')
        (η : MulAut (adjointGroup TwistTag.E6.tag K')),
        (∀ x : adjointGroup TwistTag.E6.tag K', (η x : ModGL TwistTag.E6.tag K') =
          diagramMap TwistTag.E6 K' * x * (diagramMap TwistTag.E6 K')⁻¹) →
        ∀ (hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K')
          (φ : MulAut (adjointGroup TwistTag.E6.tag K')),
          φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ ≠ MulAut.conj ⟨_, hx⟩ * η

@[expose] def TwistedE6RowXiExclusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    TwistedE6RowKinds e t f →
    ∀ (K' : Type) [Field K'] [Finite K'] (σ' : K' ≃+* K'), Nat.card K' = (2 ^ f) ^ 2 →
      (∀ c, σ' c = c ^ (2 ^ f)) →
      Nonempty (pieceSpan e ⧸ center (pieceSpan e) ≃*
        graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom) →
      t ∉ pieceSpan e →
      ∀ M : Subgroup G, (∃ g : G, M = CFSG.conjugate (pieceSpan e) g) →
      ∀ (htM : t ∈ normalizer (M : Set G))
        (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom)
        (hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈
          graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom)
        (φ η : MulAut (graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom)),
        (∀ x : graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom,
          (η x : ModGL TwistTag.E6.tag K') =
            diagramMap TwistTag.E6 K' * x * (diagramMap TwistTag.E6 K')⁻¹) →
        φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ ≠ MulAut.conj ⟨_, hx⟩ * η

@[expose] def TwistedE6RowInnerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    TwistedE6RowKinds e t f →
    ∀ (K' : Type) [Field K'] [Finite K'] (σ' : K' ≃+* K'), Nat.card K' = (2 ^ f) ^ 2 →
      (∀ c, σ' c = c ^ (2 ^ f)) →
      Nonempty (pieceSpan e ⧸ center (pieceSpan e) ≃*
        graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom) →
      t ∉ pieceSpan e →
      ∀ M : Subgroup G, (∃ g : G, M = CFSG.conjugate (pieceSpan e) g) →
      ∀ (htM : t ∈ normalizer (M : Set G))
        (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom),
        normalizerQuotMulAut eM ⟨t, htM⟩ ∉
          (MulAut.conj : graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom →* _).range

end Inputs

section Derive

theorem eq_conjugate_one {G : Type} [Group G] (H : Subgroup G) : H = CFSG.conjugate H 1 := by
  ext x
  rw [mem_conjugate_iff_of_mul, one_mul, inv_one, mul_one]


theorem e6RowUniqueQuotInput_of_xi (hξ : E6RowXiExclusionInput) : E6RowUniqueQuotInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk K' _ _ hK' he₆
  obtain ⟨e₀⟩ := he₆
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hG₀ := commutator_pieceSpan e
  have hLG₀ := le_pieceSpan hq e
  have htN : t ∈ normalizer (pieceSpan e : Set G) :=
    mem_normalizer_iSup fun J => le_normalizer_pieceCore e hw.mem_centralizer J.1
  have h36 : 2 ^ (36 * f) ∣ Nat.card (adjointGroup Tag.E6 K') := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hK']
    obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordE6' (by omega : 1 ≤ f)).two
    rw [hr, mul_comm 36 f]
    exact Dvd.intro r rfl
  have htC : t ∉ centralizer (pieceSpan e : Set G) :=
    not_mem_centralizer_of_two_pow_dvd_quot hw.standard hw.one_le hw.card_eq e
      hw.mem_centralizer hw.orderOf_eq hG₀ e₀ h36
  have hZ := odd_card_center_of_odd_card_centralizer (odd_card_centralizer_pieceSpan hw e hLG₀ htC)
  have hξ' := hξ G L K e t f hw hf hk K' hK' ⟨e₀⟩
  rcases inf_centralizer_eq_or_xi_E6_quot hw.standard hf hw.card_eq e hw.mem_centralizer
      hw.orderOf_eq hw.inf_eq hG₀ hZ hK' e₀ htN with ⟨hC₀, η, hη, φ₀, hφ₀⟩ | ⟨η', hη', hx, φ, hφ⟩
  · refine unique_of_eta_of_conjugates hf hw.card_eq e hw.orderOf_eq hZ e₀ η htN
      ⟨hC₀, φ₀, hφ₀⟩ fun g htM => ?_
    have hMp := E6Pilot.commutator_conjugate_eq hG₀ g⁻¹
    have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g⁻¹))) := by
      rw [E6Pilot.card_center_conjugate]
      exact hZ
    rcases inf_centralizer_eq_or_xi_E6_quot hw.standard hf hw.card_eq e hw.mem_centralizer
        hw.orderOf_eq hw.inf_eq hMp hZM hK'
        ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹).symm.trans e₀) htM with
      ⟨hCM, η₁, hη₁, φ₁, hφ₁⟩ | ⟨η₁, hη₁, hx, φ₁, hφ₁⟩
    · have h1 : η₁ = η := MulEquiv.ext fun x => Subtype.ext ((hη₁ x).trans (hη x).symm)
      exact ⟨hCM, φ₁, h1 ▸ hφ₁⟩
    · exact absurd hφ₁ (hξ' _ ⟨g⁻¹, rfl⟩ htM _ η₁ hη₁ hx φ₁)
  · exact absurd hφ (hξ' _ ⟨1, eq_conjugate_one _⟩ htN e₀ η' hη' hx φ)

theorem twistedE6RowUniqueQuotInput_of_xi (hin : TwistedE6RowInnerInput)
    (hξ : TwistedE6RowXiExclusionInput) : TwistedE6RowUniqueQuotInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk K' _ _ σ' hK' hσ' he₆ htG
  obtain ⟨e₀⟩ := he₆
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hG₀ := commutator_pieceSpan e
  have hLG₀ := le_pieceSpan hq e
  have htN : t ∈ normalizer (pieceSpan e : Set G) :=
    mem_normalizer_iSup fun J => le_normalizer_pieceCore e hw.mem_centralizer J.1
  have hin' := hin G L K e t f hw hf hk K' σ' hK' hσ' ⟨e₀⟩ htG
  have hξ' := hξ G L K e t f hw hf hk K' σ' hK' hσ' ⟨e₀⟩ htG
  have hout₀ := hin' _ ⟨1, eq_conjugate_one _⟩ htN e₀
  have htC : t ∉ centralizer (pieceSpan e : Set G) := fun h => hout₀
    ⟨1, by rw [map_one, EPilot.normalizerQuotMulAut_eq_one_of_mem_centralizer e₀ htN h]⟩
  have hZ := odd_card_center_of_odd_card_centralizer (odd_card_centralizer_pieceSpan hw e hLG₀ htC)
  rcases inf_centralizer_eq_or_xi_twistedE6_quot hw.standard hw.card_eq e hw.mem_centralizer
      hw.orderOf_eq hw.inf_eq hZ hK' σ'.toRingHom hσ' e₀ htN hout₀ with
    ⟨hC₀, η, hη, φ₀, hφ₀⟩ | ⟨hx, φ, η', hη', hφ⟩
  · refine unique_of_eta_of_conjugates hf hw.card_eq e hw.orderOf_eq hZ e₀ η htN
      ⟨hC₀, φ₀, hφ₀⟩ fun g htM => ?_
    have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g⁻¹))) := by
      rw [E6Pilot.card_center_conjugate]
      exact hZ
    have hout := hin' _ ⟨g⁻¹, rfl⟩ htM
      ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹).symm.trans e₀)
    rcases inf_centralizer_eq_or_xi_twistedE6_quot hw.standard hw.card_eq e hw.mem_centralizer
        hw.orderOf_eq hw.inf_eq hZM hK' σ'.toRingHom hσ'
        ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹).symm.trans e₀) htM hout with
      ⟨hCM, η₁, hη₁, φ₁, hφ₁⟩ | ⟨hx, φ₁, η₁, hη₁, hφ₁⟩
    · have h1 : η₁ = η := MulEquiv.ext fun x => Subtype.ext ((hη₁ x).trans (hη x).symm)
      exact ⟨hCM, φ₁, h1 ▸ hφ₁⟩
    · exact absurd hφ₁ (hξ' _ ⟨g⁻¹, rfl⟩ htM _ hx φ₁ η₁ hη₁)
  · exact absurd hφ (hξ' _ ⟨1, eq_conjugate_one _⟩ htN e₀ hx φ η' hη')

end Derive

end CFSG.SeitzReduction.F4Pilot
