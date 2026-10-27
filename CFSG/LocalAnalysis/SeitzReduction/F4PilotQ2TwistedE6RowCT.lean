module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedDatum twistedRootGroup)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

set_option linter.unusedSectionVars false

section Family

variable {G : Type} [Group G]

structure IsTwistedE6TwoFamily (t : G) (k : Type) [Field k] (θ : k →+* k)
    (φ : ∀ J, (twistedDatum k θ).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (twistedDatum k θ).leviAmalgam φ
  conj : ∀ (i : Fin (Tag.rank .F4))
    (x y : CFSG.LieType.CurtisTits.levi (twistedDatum k θ).rootGroup {i}),
    (y : fixedGroup k θ) = sigmaHat θ x →
      t * φ ⟨{i}, card_singleton_le_two_F4 i⟩ x * t⁻¹ = φ ⟨{i}, card_singleton_le_two_F4 i⟩ y

@[expose] noncomputable def twoFamilySpan {k : Type} [Field k] {θ : k →+* k}
    (φ : ∀ J, (twistedDatum k θ).leviAmalgam J →* G) : Subgroup G :=
  ⨆ J, (φ J).range

theorem mem_twoFamilySpan {k : Type} [Field k] {θ : k →+* k}
    (φ : ∀ J, (twistedDatum k θ).leviAmalgam J →* G) (J : _) (x : _) :
    φ J x ∈ twoFamilySpan φ :=
  le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩

theorem exists_ne_one_of_twoFamilySpan_ne_bot {k : Type} [Field k] {θ : k →+* k}
    {φ : ∀ J, (twistedDatum k θ).leviAmalgam J →* G} (hne : twoFamilySpan φ ≠ ⊥) :
    ∃ J, ∃ x, φ J x ≠ 1 := by
  by_contra h
  push Not at h
  apply hne
  rw [twoFamilySpan, eq_bot_iff]
  refine iSup_le fun J => ?_
  rintro _ ⟨x, rfl⟩
  exact mem_bot.2 (h J x)

end Family

section Recognition

variable {G : Type} [Group G]

theorem exists_center_quotient_outer_of_isTwistedE6TwoFamily {f : ℕ} (hf : 1 ≤ f)
    {k : Type} [Field k] [Finite k] (hK : Nat.card k = (2 ^ f) ^ 2) (σ' : k ≃+* k)
    (hσ : ∀ c, σ' c = c ^ (2 ^ f)) {t : G}
    {φ : ∀ J, (twistedDatum k σ'.toRingHom).leviAmalgam J →* G}
    (hφ : IsTwistedE6TwoFamily t k σ'.toRingHom φ) (hnt : ∃ J, ∃ x, φ J x ≠ 1) :
    CFSG.IsQuasisimple (twoFamilySpan φ) ∧
    ∃ (e₆ : twoFamilySpan φ ⧸ center (twoFamilySpan φ) ≃*
        graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)
      (htN : t ∈ normalizer (twoFamilySpan φ : Set G)),
      normalizerQuotMulAut e₆ ⟨t, htN⟩ = fieldActor σ' σ' ∧
        normalizerQuotMulAut e₆ ⟨t, htN⟩ ∉
          (MulAut.conj : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom →* _).range := by
  have hσθ : ∀ c, σ'.toRingHom c = c ^ (2 ^ f) := hσ
  have hinv := involutive_of_natCard_eq hK hσθ
  have hk4 := four_le_natCard_of_eq hf hK
  set G₀ := twoFamilySpan φ with hG₀
  have hle : ∀ J y, φ J y ∈ G₀ := fun J y => mem_twoFamilySpan φ J y
  set φ' : ∀ J, (twistedDatum k σ'.toRingHom).leviAmalgam J →* G₀ :=
    fun J => (φ J).codRestrict G₀ (hle J) with hφ'def
  have hφ' : IsCompatible (twistedDatum k σ'.toRingHom).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ.compatible i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans (rfl : (⨆ J, (φ J).range) = G₀)
    rw [← MonoidHom.range_comp]
    rfl
  have hnt' : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨J, x, hx⟩ := hnt
    exact ⟨J, x, fun h => hx (congrArg Subtype.val h)⟩
  obtain ⟨ψ, hψ, hsurj, hker, hq, hZ⟩ :=
    exists_surjective_of_isCompatible_twistedE6 k σ'.toRingHom hinv hk4 φ' hφ' hgen' hnt'
  have hψφ : ∀ J (y : (twistedDatum k σ'.toRingHom).leviAmalgam J), ((ψ y : G₀) : G) = φ J y :=
    fun J y => congrArg Subtype.val (hψ J y)
  have hgenR : Subgroup.closure (⋃ i, (CFSG.LieType.CurtisTits.rankOne
      (twistedDatum k σ'.toRingHom).rootGroup i : Set (fixedGroup k σ'.toRingHom))) = ⊤ := by
    rw [← Subgroup.iSup_eq_closure, eq_top_iff]
    have hct := CFSG.LieType.Steinberg.TwistedE6.twistedDatum_isCTGroupDatum σ'.toRingHom hinv
      (CFSG.LieType.Steinberg.TwistedE6.iSup_twistedDatum_rootGroup σ'.toRingHom hinv)
    rw [← CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem (twistedDatum k σ'.toRingHom).isFiniteType
        (twistedDatum k σ'.toRingHom).divisible) hct]
    exact iSup_le fun J => iSup₂_le fun j _ =>
      le_iSup (fun i => CFSG.LieType.CurtisTits.rankOne (twistedDatum k σ'.toRingHom).rootGroup i) j
  have hconj : ∀ g, t * (ψ g : G) * t⁻¹ = ψ (sigmaHat σ'.toRingHom g) := by
    have h : (MulAut.conj t).toMonoidHom.comp (G₀.subtype.comp ψ) =
        G₀.subtype.comp (ψ.comp (sigmaHat σ'.toRingHom)) := by
      refine MonoidHom.eq_of_eqOn_dense hgenR ?_
      intro g hg
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hg
      have hx : g ∈ CFSG.LieType.CurtisTits.levi (twistedDatum k σ'.toRingHom).rootGroup {i} := by
        rw [CFSG.LieType.CurtisTits.levi_singleton]
        exact hi
      have hy : sigmaHat σ'.toRingHom g ∈
          CFSG.LieType.CurtisTits.levi (twistedDatum k σ'.toRingHom).rootGroup {i} := by
        rw [CFSG.LieType.CurtisTits.levi_singleton]
        exact sigmaHat_mem_rankOne σ'.toRingHom hi
      have h1 : ((ψ g : G₀) : G) = φ ⟨{i}, card_singleton_le_two_F4 i⟩ ⟨g, hx⟩ :=
        hψφ ⟨{i}, card_singleton_le_two_F4 i⟩ ⟨g, hx⟩
      have h2 : ((ψ (sigmaHat σ'.toRingHom g) : G₀) : G) =
          φ ⟨{i}, card_singleton_le_two_F4 i⟩ ⟨_, hy⟩ :=
        hψφ ⟨{i}, card_singleton_le_two_F4 i⟩ ⟨_, hy⟩
      have h3 := hφ.conj i ⟨g, hx⟩ ⟨_, hy⟩ rfl
      change t * ((ψ g : G₀) : G) * t⁻¹ = ((ψ (sigmaHat σ'.toRingHom g) : G₀) : G)
      rw [h1, h2]
      exact h3
    intro g
    exact DFunLike.congr_fun h g
  have hσσ : ∀ g, sigmaHat σ'.toRingHom (sigmaHat σ'.toRingHom g) = g := fun g =>
    Subtype.ext (CFSG.LieType.Steinberg.TwistedE6.sigma_sigma (RingHom.id k) (fun _ => rfl)
      (g : e6Data_valid.minGroup k))
  have htN : t ∈ normalizer (G₀ : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨g, hg⟩ := hsurj ⟨x, hx⟩
      have hgx : ((ψ g : G₀) : G) = x := congrArg Subtype.val hg
      rw [← hgx, hconj g]
      exact (ψ _).2
    · intro hx
      obtain ⟨g, hg⟩ := hsurj ⟨t * x * t⁻¹, hx⟩
      have hgx : ((ψ g : G₀) : G) = t * x * t⁻¹ := congrArg Subtype.val hg
      have h1 := hconj (sigmaHat σ'.toRingHom g)
      rw [hσσ, hgx] at h1
      have h2 : ((ψ (sigmaHat σ'.toRingHom g) : G₀) : G) = x :=
        mul_left_cancel (mul_right_cancel h1)
      rw [← h2]
      exact (ψ _).2
  set π := twistedIsogenyC hf hK σ'.toRingHom hσθ with hπ
  set Ψ : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom ≃* G₀ ⧸ center G₀ :=
    (twistedCenterQuotientEquiv hf hK σ'.toRingHom hσθ).symm.trans
      (E6Pilot.centerQuotientMulEquiv ψ hsurj hker hZ) with hΨ
  have hΨπ : ∀ s, Ψ (π s) = QuotientGroup.mk (ψ s) := by
    intro s
    rw [hΨ, MulEquiv.trans_apply, hπ, ← twistedCenterQuotientEquiv_mk,
      MulEquiv.symm_apply_apply, E6Pilot.centerQuotientMulEquiv_mk]
  have hact : ∀ s, normalizerQuotMulAut Ψ.symm ⟨t, htN⟩ (π s) = π (sigmaHat σ'.toRingHom s) := by
    intro s
    have h1 : π s = Ψ.symm (QuotientGroup.mk' (center G₀) (ψ s)) := by
      rw [QuotientGroup.mk'_apply, ← hΨπ, MulEquiv.symm_apply_apply]
    have h2 : G₀.normalizerMonoidHom ⟨t, htN⟩ (ψ s) = ψ (sigmaHat σ'.toRingHom s) :=
      Subtype.ext ((Subgroup.normalizerMonoidHom_apply_apply_coe G₀ _ _).trans (hconj s))
    rw [h1, normalizerQuotMulAut_apply, h2, QuotientGroup.mk'_apply, ← hΨπ,
      MulEquiv.symm_apply_apply]
  have heq : normalizerQuotMulAut Ψ.symm ⟨t, htN⟩ = fieldActor σ' σ' := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hP, -, -, -, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf k hK σ' hσ
    refine MulEquiv.ext fun c => ?_
    obtain ⟨s, rfl⟩ := twistedIsogenyC_surjective hf hK σ'.toRingHom hσθ c
    rw [hact]
    apply Subtype.ext
    rw [hP, coe_twistedIsogenyC_sigmaHat]
  refine ⟨hq, Ψ.symm, htN, heq, ?_⟩
  rw [heq]
  exact fieldActor_self_not_mem_range_conj hf hK σ' hσ

end Recognition

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G}

theorem false_of_isTwistedE6TwoFamily {f : ℕ} (hw : F4Work L K t f) {k : Type} [Field k]
    [Finite k] (hK : Nat.card k = (2 ^ f) ^ 2) (σ' : k ≃+* k) (hσ : ∀ c, σ' c = c ^ (2 ^ f))
    {φ : ∀ J, (twistedDatum k σ'.toRingHom).leviAmalgam J →* G}
    (hφ : IsTwistedE6TwoFamily t k σ'.toRingHom φ) (hL : L ≤ twoFamilySpan φ)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (twoFamilySpan φ : Set G) →
      g ∈ normalizer (twoFamilySpan φ : Set G)) : False := by
  have hLne : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨-, -, -, -, h⟩ := hw.standard.standard
    exact h 1 (Subgroup.commutator_bot_left _)
  have hne : twoFamilySpan φ ≠ ⊥ := fun h => hLne (eq_bot_iff.2 (h ▸ hL))
  obtain ⟨hq, e₆, htN, -, hout⟩ := exists_center_quotient_outer_of_isTwistedE6TwoFamily hw.one_le
    hK σ' hσ hφ (exists_ne_one_of_twoFamilySpan_ne_bot hne)
  have htC : t ∉ centralizer (twoFamilySpan φ : Set G) := fun htC =>
    hout ⟨1, by rw [map_one, EPilot.normalizerQuotMulAut_eq_one_of_mem_centralizer e₆ htN htC]⟩
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hw.inf_eq hL hw.orderOf_eq htN htC
  have : Group.IsPerfect (twoFamilySpan φ) := hq.1
  have := hw.standard.simple
  exact EPilot.false_of_simple_of_twistedE6_quot hZ hw.one_le k hK σ' hσ e₆ htN hw.orderOf_eq
    hout huniq

theorem false_of_isTwistedE6TwoFamily_two (hw : F4Work L K t 1) {k : Type} [Field k] [Finite k]
    (hK : Nat.card k = 4) (σ' : k ≃+* k) (hσ : ∀ c, σ' c = c ^ 2)
    {φ : ∀ J, (twistedDatum k σ'.toRingHom).leviAmalgam J →* G}
    (hφ : IsTwistedE6TwoFamily t k σ'.toRingHom φ) (hL : L ≤ twoFamilySpan φ)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (twoFamilySpan φ : Set G) →
      g ∈ normalizer (twoFamilySpan φ : Set G)) : False :=
  false_of_isTwistedE6TwoFamily hw (by rw [hK]; norm_num) σ' (fun c => by rw [hσ, pow_one]) hφ
    hL huniq

end Endgame

end CFSG.SeitzReduction.F4Pilot
