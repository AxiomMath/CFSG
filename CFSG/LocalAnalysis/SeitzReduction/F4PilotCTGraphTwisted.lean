module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphE6

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rhoPerm rho fixedGroup mem_fixedGroup twistedDatum
  twistedRootGroup sigma_xm_single sigma_xm_neg_single)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

section Sigma


variable {k : Type} [Field k] (θ : k →+* k)

theorem sigma_id_comm (g : e6Data_valid.minGroup k) :
    sigma k (RingHom.id k) (sigma k θ g) = sigma k θ (sigma k (RingHom.id k) g) := by
  have h : (sigma k (RingHom.id k)).comp (sigma k θ) =
      (sigma k θ).comp (sigma k (RingHom.id k)) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid k) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, sigma_xm_single, RingHom.id_apply]
    · simp only [MonoidHom.comp_apply, sigma_xm_neg_single, RingHom.id_apply]
  exact DFunLike.congr_fun h g

theorem sigma_id_mem_fixedGroup {g : e6Data_valid.minGroup k} (hg : g ∈ fixedGroup k θ) :
    sigma k (RingHom.id k) g ∈ fixedGroup k θ := by
  rw [mem_fixedGroup] at hg ⊢
  rw [← sigma_id_comm, hg]

@[expose] noncomputable def sigmaHat : fixedGroup k θ →* fixedGroup k θ :=
  ((sigma k (RingHom.id k)).comp (fixedGroup k θ).subtype).codRestrict (fixedGroup k θ)
    fun g => sigma_id_mem_fixedGroup θ g.2

theorem coe_sigmaHat (g : fixedGroup k θ) :
    ((sigmaHat θ g : fixedGroup k θ) : e6Data_valid.minGroup k) = sigma k (RingHom.id k) g :=
  rfl

theorem sigmaHat_mem_twistedRootGroup {β : Fin (Tag.rank .F4) → ℤ} {x : fixedGroup k θ}
    (hx : x ∈ twistedRootGroup k θ β) : sigmaHat θ x ∈ twistedRootGroup k θ β := by
  rw [twistedRootGroup, Subgroup.mem_subgroupOf, twistedRootSubgroup, Subgroup.mem_inf] at hx ⊢
  refine ⟨?_, sigma_id_mem_fixedGroup θ hx.2⟩
  have hle : (⨆ α ∈ {α : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α = c • β),
        e6Data_valid.rootGroup k α) ≤
      (⨆ α ∈ {α : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 α},
        ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α = c • β),
          e6Data_valid.rootGroup k α).comap (sigma k (RingHom.id k)) := by
    refine iSup₂_le fun α hα => iSup_le fun hc => ?_
    intro y hy
    rw [Subgroup.mem_comap]
    have hy' := CFSG.LieType.Steinberg.TwistedE6.sigma_mem_rootGroup_rho (θ := RingHom.id k) hα hy
    obtain ⟨c, hc0, hcα⟩ := hc
    refine le_iSup₂_of_le (f := fun α (_ : α ∈ {α : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 α}) =>
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum CFSG.LieType.Steinberg.TwistedE6.orbitMap α = c • β),
        e6Data_valid.rootGroup k α) (rho α)
      (CFSG.LieType.Steinberg.TwistedE6.isRoot_rho hα) (le_iSup_of_le ⟨c, hc0, ?_⟩ le_rfl) hy'
    rw [← CFSG.LieType.Steinberg.TwistedE6.proj_apply, CFSG.LieType.Steinberg.TwistedE6.proj_rho,
      CFSG.LieType.Steinberg.TwistedE6.proj_apply, hcα]
  exact hle hx.1

theorem sigmaHat_mem_rankOne {i : Fin (Tag.rank .F4)} {x : fixedGroup k θ}
    (hx : x ∈ CFSG.LieType.CurtisTits.rankOne (twistedRootGroup k θ) i) :
    sigmaHat θ x ∈ CFSG.LieType.CurtisTits.rankOne (twistedRootGroup k θ) i := by
  have hle : CFSG.LieType.CurtisTits.rankOne (twistedRootGroup k θ) i ≤
      (CFSG.LieType.CurtisTits.rankOne (twistedRootGroup k θ) i).comap (sigmaHat θ) :=
    sup_le (fun y hy => mem_sup_left (sigmaHat_mem_twistedRootGroup θ hy))
      (fun y hy => mem_sup_right (sigmaHat_mem_twistedRootGroup θ hy))
  exact hle hx

end Sigma

section Recognition


variable (k : Type) [Field k] [Finite k] (θ : k →+* k)

theorem exists_surjective_of_isCompatible_twistedE6 (hθ : ∀ c, θ (θ c) = c)
    (hk : 4 ≤ Nat.card k) {G : Type} [Group G]
    (φ : ∀ J, (twistedDatum k θ).leviAmalgam J →* G)
    (hφ : IsCompatible (twistedDatum k θ).leviAmalgam φ) (hgen : ⨆ J, (φ J).range = ⊤)
    (hnt : ∃ J, ∃ x, φ J x ≠ 1) :
    ∃ ψ : fixedGroup k θ →* G, (∀ J (x : (twistedDatum k θ).leviAmalgam J), ψ x = φ J x) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ center (fixedGroup k θ) ∧ CFSG.IsQuasisimple G ∧
      center G = (center (fixedGroup k θ)).map ψ := by
  have hct := CFSG.LieType.Steinberg.TwistedE6.twistedDatum_isCTGroupDatum θ hθ
    (CFSG.LieType.Steinberg.TwistedE6.iSup_twistedDatum_rootGroup θ hθ)
  have hext := CFSG.LieType.Steinberg.TwistedE6.twistedDatum_steinbergExtras θ hθ
  have hgenK : ⨆ J, (twistedDatum k θ).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem (twistedDatum k θ).isFiniteType
        (twistedDatum k θ).divisible) hct
  have hU : CFSG.LieType.CurtisTits.IsUniversalCompletion.{0, 0, 0}
      (twistedDatum k θ).leviAmalgam :=
    (twistedDatum k θ).isUniversalCompletion_of_steinbergPresentation hct
      (steinbergPresentation_of_extras hct hext)
  obtain ⟨ψ, hψ, hsurj, hker, hq, hZ, -⟩ :=
    CFSG.LieType.CurtisTits.recognition_of_isUniversalCompletion hgenK
      (CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isQuasisimple_of_four_le_card θ hθ hk) hU φ hφ
      hgen hnt
  exact ⟨ψ, hψ, hsurj, hker, hq, hZ⟩

end Recognition

section Isogeny


variable {k : Type} [Field k] [Finite k] {f : ℕ}

theorem involutive_of_natCard_eq (hK : Nat.card k = (2 ^ f) ^ 2) {θ : k →+* k}
    (hσ : ∀ c, θ c = c ^ (2 ^ f)) (c : k) : θ (θ c) = c := by
  have : Fintype k := Fintype.ofFinite k
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

omit
  [Field k] [Finite k] in
theorem four_le_natCard_of_eq (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2) : 4 ≤ Nat.card k := by
  rw [hK]
  have h2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  nlinarith

theorem range_e6IsogenyFixed_eq_graphFixedRootGroup (hf : 1 ≤ f)
    (hK : Nat.card k = (2 ^ f) ^ 2) {θ : k →+* k} (hσ : ∀ c, θ c = c ^ (2 ^ f)) :
    (e6IsogenyFixed θ).range = graphFixedRootGroup TwistTag.E6 k θ := by
  rw [range_e6IsogenyFixed θ (involutive_of_natCard_eq hK hσ) (four_le_natCard_of_eq hf hK)]
  exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf k hK θ hσ).2.2.1

@[expose] noncomputable def twistedIsogenyC (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2)
    (θ : k →+* k) (hσ : ∀ c, θ c = c ^ (2 ^ f)) :
    fixedGroup k θ →* graphFixedRootGroup TwistTag.E6 k θ :=
  (e6IsogenyFixed θ).codRestrict _ fun g => by
    rw [← range_e6IsogenyFixed_eq_graphFixedRootGroup hf hK hσ]
    exact ⟨g, rfl⟩

theorem coe_twistedIsogenyC (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2) (θ : k →+* k)
    (hσ : ∀ c, θ c = c ^ (2 ^ f)) (g : fixedGroup k θ) :
    ((twistedIsogenyC hf hK θ hσ g : graphFixedRootGroup TwistTag.E6 k θ) :
      ModGL TwistTag.E6.tag k) =
      ((e6IsogenyT k g : adjointGroup TwistTag.E6.tag k) : ModGL TwistTag.E6.tag k) :=
  rfl

theorem twistedIsogenyC_surjective (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2) (θ : k →+* k)
    (hσ : ∀ c, θ c = c ^ (2 ^ f)) : Function.Surjective (twistedIsogenyC hf hK θ hσ) := by
  rintro ⟨y, hy⟩
  rw [← range_e6IsogenyFixed_eq_graphFixedRootGroup hf hK hσ] at hy
  obtain ⟨g, rfl⟩ := hy
  exact ⟨g, rfl⟩

theorem coe_twistedIsogenyC_sigmaHat (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2) (θ : k →+* k)
    (hσ : ∀ c, θ c = c ^ (2 ^ f)) (g : fixedGroup k θ) :
    ((twistedIsogenyC hf hK θ hσ (sigmaHat θ g) : graphFixedRootGroup TwistTag.E6 k θ) :
      ModGL TwistTag.E6.tag k) = diagramMap TwistTag.E6 k *
        (twistedIsogenyC hf hK θ hσ g : ModGL TwistTag.E6.tag k) *
          (diagramMap TwistTag.E6 k)⁻¹ := by
  rw [coe_twistedIsogenyC, coe_twistedIsogenyC, coe_sigmaHat, e6IsogenyT_sigma (RingHom.id k),
    coe_twistC, CFSG.LieType.Chevalley.twistHom_id_eq]

theorem exists_twistedIsogenyC_ne_one (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2)
    (θ : k →+* k) (hσ : ∀ c, θ c = c ^ (2 ^ f)) : ∃ g, twistedIsogenyC hf hK θ hσ g ≠ 1 := by
  set i : Fin (Tag.rank .E6) := ⟨1, by decide⟩
  have hfix : e6Data_valid.xm k (Pi.single i 1) 1 ∈ fixedGroup k θ := by
    rw [mem_fixedGroup, sigma_xm_single, map_one]
    rfl
  refine ⟨⟨_, hfix⟩, fun h => ?_⟩
  have h' := congrArg (fun y : graphFixedRootGroup TwistTag.E6 k θ =>
    (y : ModGL TwistTag.E6.tag k)) h
  simp only [coe_twistedIsogenyC, OneMemClass.coe_one] at h'
  exact e6Isogeny_xm_single_one_ne_one _ i (Subtype.ext h')

theorem ker_twistedIsogenyC (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2) (θ : k →+* k)
    (hσ : ∀ c, θ c = c ^ (2 ^ f)) :
    (twistedIsogenyC hf hK θ hσ).ker = center (fixedGroup k θ) := by
  refine le_antisymm (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isQuasisimple_of_four_le_card θ
      (involutive_of_natCard_eq hK hσ) (four_le_natCard_of_eq hf hK))
    (exists_twistedIsogenyC_ne_one hf hK θ hσ)) fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hzc : twistedIsogenyC hf hK θ hσ z ∈ center (graphFixedRootGroup TwistTag.E6 k θ) :=
    mem_center_iff.2 fun a => by
      obtain ⟨g, rfl⟩ := twistedIsogenyC_surjective hf hK θ hσ a
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective θ.injective),
    mem_bot] at hzc
  exact hzc

@[expose] noncomputable def twistedCenterQuotientEquiv (hf : 1 ≤ f)
    (hK : Nat.card k = (2 ^ f) ^ 2) (θ : k →+* k) (hσ : ∀ c, θ c = c ^ (2 ^ f)) :
    fixedGroup k θ ⧸ center (fixedGroup k θ) ≃* graphFixedRootGroup TwistTag.E6 k θ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_twistedIsogenyC hf hK θ hσ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (twistedIsogenyC_surjective hf hK θ hσ))

theorem twistedCenterQuotientEquiv_mk (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2)
    (θ : k →+* k) (hσ : ∀ c, θ c = c ^ (2 ^ f)) (x : fixedGroup k θ) :
    twistedCenterQuotientEquiv hf hK θ hσ (QuotientGroup.mk x) = twistedIsogenyC hf hK θ hσ x :=
  rfl

end Isogeny

theorem card_singleton_le_two_F4 (i : Fin (Tag.rank .F4)) :
    ({i} : Finset (Fin (Tag.rank .F4))).card ≤ 2 := by
  simp

section Family


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

structure IsTwistedE6GraphRowFamily (e : L ≃* adjointGroup .F4 K) (t : G) (k : Type) [Field k]
    (θ : k →+* k) (φ : ∀ J, (twistedDatum k θ).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (twistedDatum k θ).leviAmalgam φ
  iSup_range : ⨆ J, (φ J).range = pieceSpan e
  conj : ∀ (i : Fin (Tag.rank .F4))
    (x y : CFSG.LieType.CurtisTits.levi (twistedDatum k θ).rootGroup {i}),
    (y : fixedGroup k θ) = sigmaHat θ x →
      t * φ ⟨{i}, card_singleton_le_two_F4 i⟩ x * t⁻¹ = φ ⟨{i}, card_singleton_le_two_F4 i⟩ y

end Family

section Main


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem fieldActor_self_not_mem_range_conj {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k] [Finite k]
    (hK : Nat.card k = (2 ^ f) ^ 2) (σ' : k ≃+* k) (hσ : ∀ c, σ' c = c ^ (2 ^ f)) :
    fieldActor σ' σ' ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom →* _).range := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf k hK σ' hσ
  rintro ⟨c, hc⟩
  have h1 : Θ (fieldActor σ' σ') = σ' :=
    hΘ _ 1 1 σ' (by rw [map_one, map_one, one_mul, one_mul])
  have h2 : Θ (MulAut.conj c) = 1 := by
    have hmem : MulAut.conj c ∈ Θ.ker := by
      rw [hker]
      exact mem_sup_left
        (show MulAut.conj c ∈
            (MulAut.conj : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom →* _).range
          from ⟨c, rfl⟩)
    exact hmem
  rw [← hc, h2] at h1
  obtain ⟨σ₀, hσ₀, hord, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf k hK
  have hσσ : σ₀ = σ' := RingEquiv.ext fun c => by rw [hσ₀, hσ]
  rw [hσσ, ← h1, orderOf_one] at hord
  exact absurd hord (by decide)

theorem exists_center_quotient_outer_of_isTwistedE6GraphRowFamily {f : ℕ} (hf : 1 ≤ f)
    {k : Type} [Field k] [Finite k] (hK : Nat.card k = (2 ^ f) ^ 2) (σ' : k ≃+* k)
    (hσ : ∀ c, σ' c = c ^ (2 ^ f)) {e : L ≃* adjointGroup .F4 K} {t : G}
    (htL : t ∈ centralizer (L : Set G)) (hne : pieceSpan e ≠ ⊥)
    {φ : ∀ J, (twistedDatum k σ'.toRingHom).leviAmalgam J →* G}
    (hφ : IsTwistedE6GraphRowFamily e t k σ'.toRingHom φ) :
    ∃ (e₆ : pieceSpan e ⧸ center (pieceSpan e) ≃*
        graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)
      (htN : t ∈ normalizer (pieceSpan e : Set G)),
      normalizerQuotMulAut e₆ ⟨t, htN⟩ = fieldActor σ' σ' ∧
        normalizerQuotMulAut e₆ ⟨t, htN⟩ ∉
          (MulAut.conj : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom →* _).range := by
  have hσθ : ∀ c, σ'.toRingHom c = c ^ (2 ^ f) := hσ
  have hinv := involutive_of_natCard_eq hK hσθ
  have hk4 := four_le_natCard_of_eq hf hK
  set G₀ := pieceSpan e with hG₀
  have hle : ∀ J y, φ J y ∈ G₀ := fun J y => by
    rw [hG₀, ← hφ.iSup_range]
    exact le_iSup (fun J => (φ J).range) J ⟨y, rfl⟩
  set φ' : ∀ J, (twistedDatum k σ'.toRingHom).leviAmalgam J →* G₀ :=
    fun J => (φ J).codRestrict G₀ (hle J) with hφ'def
  have hφ' : IsCompatible (twistedDatum k σ'.toRingHom).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ.compatible i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hφ.iSup_range
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    rw [hG₀, ← hφ.iSup_range, eq_bot_iff]
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    exact mem_bot.2 (congrArg Subtype.val (h J x))
  obtain ⟨ψ, hψ, hsurj, hker, -, hZ⟩ :=
    exists_surjective_of_isCompatible_twistedE6 k σ'.toRingHom hinv hk4 φ' hφ' hgen' hnt
  have hψφ : ∀ J (y : (twistedDatum k σ'.toRingHom).leviAmalgam J), ((ψ y : G₀) : G) = φ J y :=
    fun J y => congrArg Subtype.val (hψ J y)
  have htN : t ∈ normalizer (G₀ : Set G) :=
    mem_normalizer_iSup fun J => le_normalizer_pieceCore e htL J.1
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
  refine ⟨Ψ.symm, htN, heq, ?_⟩
  rw [heq]
  exact fieldActor_self_not_mem_range_conj hf hK σ' hσ

end Main

section Input


@[expose] def TwistedE6GraphRowFamilyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    TwistedE6RowKinds e t f →
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (σ' : K' ≃+* K'), Nat.card K' = (2 ^ f) ^ 2 ∧
      (∀ c, σ' c = c ^ (2 ^ f)) ∧
      ∃ φ : ∀ J, (twistedDatum K' σ'.toRingHom).leviAmalgam J →* G,
        IsTwistedE6GraphRowFamily e t K' σ'.toRingHom φ

end Input

section Reduction


theorem twistedE6RowCTQuotInput_of_familyInput (h : TwistedE6GraphRowFamilyInput) :
    TwistedE6RowCTQuotInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk
  obtain ⟨K', i1, i2, σ', hK', hσ', φ, hφ⟩ := h G L K e t f hw hf hk
  have h4 : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨e₆, htN, -, hout⟩ := exists_center_quotient_outer_of_isTwistedE6GraphRowFamily
    (by omega) hK' σ' hσ' hw.mem_centralizer (pieceSpan_ne_bot h4 e) hφ
  exact ⟨K', i1, i2, σ', hK', hσ', e₆, htN, hout⟩

end Reduction

end CFSG.SeitzReduction.F4Pilot
