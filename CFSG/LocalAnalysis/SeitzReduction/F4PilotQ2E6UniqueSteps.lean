module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6UniqueBounds
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Graph

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

section Inner

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_card_centralizer_dvd_of_inner_quot {t : G} (ht : orderOf t = 2)
    {M : Subgroup G} (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {X : Type*}
    [Group X] (eM : M ⧸ center M ≃* X) (htM : t ∈ normalizer (M : Set G)) {u : X}
    (hu : orderOf u = 2)
    (hin : normalizerQuotMulAut eM ⟨t, htM⟩ ∈ (MulAut.conj : X →* MulAut X).range) :
    ∃ ŵ : X, orderOf ŵ = 2 ∧
      Nat.card (centralizer ({ŵ} : Set X)) ∣ Nat.card (centralizer ({t} : Set G)) := by
  obtain ⟨c, hc⟩ := hin
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  obtain ⟨q₀, hq₀⟩ := eM.surjective c
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q₀
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hkey : ∀ x : M,
      (QuotientGroup.mk (β x) : M ⧸ center M) = QuotientGroup.mk (m * x * m⁻¹) := by
    intro x
    apply eM.injective
    have h1 := normalizerQuotMulAut_apply eM ⟨t, htM⟩ x
    rw [← hc, MulAut.conj_apply, ← hq₀] at h1
    simp only [QuotientGroup.mk'_apply] at h1
    rw [← h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
  have hβm := E6Pilot.eq_conj_of_mk_eq β m hkey
  have hm2 : m ^ 2 ∈ center M := by
    rw [mem_center_iff]
    intro g
    have h := E6Pilot.normalizerMonoidHom_apply_apply_of_orderOf ht htM g
    rw [← hβdef, hβm (β g), hβm g] at h
    calc g * m ^ 2 = (m * (m * g * m⁻¹) * m⁻¹) * m ^ 2 := by rw [h]
      _ = m ^ 2 * g := by rw [sq]; group
  obtain ⟨w, hw2, hwm⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm2
  have hβw : ∀ x, β x = w * x * w⁻¹ := by
    intro x
    rw [hβm]
    have hz := mem_center_iff.1 hwm (m * x * m⁻¹)
    calc m * x * m⁻¹ = (m * x * m⁻¹) * (w * m⁻¹) * (w * m⁻¹)⁻¹ := by group
      _ = (w * m⁻¹) * (m * x * m⁻¹) * (w * m⁻¹)⁻¹ := by rw [hz]
      _ = w * x * w⁻¹ := by group
  obtain ⟨w', hw'2, hw'C⟩ : ∃ w' : M, w' ^ 2 = 1 ∧ w' ∉ center M ∧
      ∀ x : M, w' * x = x * w' → t * (x : G) * t⁻¹ = x := by
    by_cases hw1 : w = 1
    · have hcentral : ∀ x : M, t * (x : G) * t⁻¹ = x := fun x => by
        have h1 : β x = x := by rw [hβw, hw1, one_mul, inv_one, mul_one]
        rw [← hβ, h1]
      obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (eM.symm u)
      have hm₀2 : m₀ ^ 2 ∈ center M := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm₀, ← map_pow, ← hu,
          pow_orderOf_eq_one, map_one]
      obtain ⟨w₀, hw₀2, hw₀m⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm₀2
      refine ⟨w₀, hw₀2, fun hw₀Z => ?_, fun x _ => hcentral x⟩
      have h1 : (QuotientGroup.mk w₀ : M ⧸ center M) = 1 := (QuotientGroup.eq_one_iff _).2 hw₀Z
      rw [E6Pilot.mk_eq_of_mul_inv_mem_center hw₀m, hm₀] at h1
      have hu1 : u = 1 := by rw [← eM.apply_symm_apply u, h1, map_one]
      rw [hu1, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · refine ⟨w, hw2, fun hwZ => ?_, fun x hx => ?_⟩
      · have h := E6Pilot.odd_orderOf_of_mem_center hZ hwZ
        rw [orderOf_eq_prime hw2 hw1] at h
        exact absurd h (by decide)
      · have h1 : β x = x := by rw [hβw, hx, mul_inv_cancel_right]
        rw [← hβ, h1]
  set ŵ : X := eM (QuotientGroup.mk w') with hŵdef
  have hŵ : orderOf ŵ = 2 := by
    refine orderOf_eq_prime ?_ fun h => hw'C.1 ?_
    · rw [hŵdef, ← map_pow, ← QuotientGroup.mk_pow, hw'2, QuotientGroup.mk_one, map_one]
    · rw [← QuotientGroup.eq_one_iff]
      apply eM.injective
      rw [map_one]
      exact h
  have hle : centralizer ({ŵ} : Set X) ≤
      (centralizer ({w'} : Set M)).map (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) := by
    intro c hc
    obtain ⟨q₁, hq₁⟩ := eM.surjective c
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    have hcom : (QuotientGroup.mk (w' * m₁) : M ⧸ center M) = QuotientGroup.mk (m₁ * w') := by
      apply eM.injective
      have h := mem_centralizer_singleton_iff.1 hc
      rw [← hq₁] at h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul]
      exact h.symm
    obtain ⟨m', hm'w, hm'm⟩ := E6Pilot.exists_commute_of_mk_commute hZ hw'2 hcom
    refine ⟨m', mem_centralizer_singleton_iff.2 hm'w.symm, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
    rw [E6Pilot.mk_eq_of_mul_inv_mem_center hm'm, hq₁]
  have hleG : (centralizer ({w'} : Set M)).map M.subtype ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1 hx
    have h := hw'C.2 x hxw.symm
    rw [mem_centralizer_singleton_iff]
    change (x : G) * t = t * x
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  refine ⟨ŵ, hŵ, (card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans ?_)⟩
  rw [← card_map_of_injective M.subtype_injective]
  exact card_dvd_of_le hleG

end Inner

section E6


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_inner_quot_E6_row_27 (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ f) (eM : M ⧸ center M ≃* adjointGroup .E6 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    normalizerQuotMulAut eM ⟨t, htM⟩ ∉
      (MulAut.conj : adjointGroup .E6 K₂ →* MulAut (adjointGroup .E6 K₂)).range := by
  have hf := one_le_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₂
  have := charP_two_of_natCard_eq_two_pow hK₂
  intro hin
  obtain ⟨ŵ, hŵ, hdvd⟩ := exists_involution_card_centralizer_dvd_of_inner_quot ht hMp hZ eM htM
    (E6Pilot.orderOf_pinnedX_one_adjointGroup (τ := .E6) (Pi.single (0 : Fin 6) 1)) hin
  exact not_two_pow_dvd_card_centralizer_F4_27 hset hf hK e htC ht hKt
    ((two_pow_dvd_card_centralizer_E6_27 hK₂ hŵ).trans hdvd)

theorem inf_centralizer_eq_or_xi_E6_quot_27 (hset : StandardSetting G L) {f : ℕ} {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ f) (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    (M ⊓ centralizer ({t} : Set G) = L ∧
      ∃ η : MulAut (adjointGroup TwistTag.E6.tag K₂),
        (∀ h : adjointGroup TwistTag.E6.tag K₂, (η h : ModGL TwistTag.E6.tag K₂) =
          diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) ∧
        ∃ φ : MulAut (adjointGroup TwistTag.E6.tag K₂),
          φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = η) ∨
      ∃ η : MulAut (adjointGroup TwistTag.E6.tag K₂),
        (∀ h : adjointGroup TwistTag.E6.tag K₂, (η h : ModGL TwistTag.E6.tag K₂) =
          diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) ∧
        ∃ (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K₂)
          (φ : MulAut (adjointGroup TwistTag.E6.tag K₂)),
          φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η := by
  have hf := one_le_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₂
  have := charP_two_of_natCard_eq_two_pow hK₂
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  have hα2 : normalizerQuotMulAut eM ⟨t, htM⟩ ^ 2 = 1 :=
    E6Pilot.normalizerQuotMulAut_sq_eq_one eM ht htM
  have hαo : normalizerQuotMulAut eM ⟨t, htM⟩ ∉ inner (adjointGroup TwistTag.E6.tag K₂) :=
    not_inner_quot_E6_row_27 hset hK e htC ht hKt hMp hZ hK₂ eM htM
  rcases E6Pilot.outer_involution_cases_E6 hf K₂ hK₂ _ hα2 hαo with
    ⟨η, hη, ⟨φ, hφ⟩ | ⟨hx, φ, hφ⟩⟩ | ⟨σ, hσ2, hσ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩
  · refine Or.inl ⟨?_, η, hη, φ, hφ⟩
    have h2 : (2 : K₂) = 0 := CharTwo.two_eq_zero
    have hcan := canonicalGraphFixedSubgroup_adjointGroup K₂ hf hK₂ h2
    obtain ⟨hperf, hcard⟩ := eqLocus_perfect_card_of_canonicalGraphFixedSubgroup hcan hη
      (graphFixedImageF4Equiv (RingHom.id K₂) h2) (CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 K₂)
    have hmap := map_eqLocus_eq_of_conj hφ
    refine inf_centralizer_eq_of_quot_of_card hset hOut htC ht hKt hZ eM htM ?_ ?_
    · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      change (⁅(normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _),
          (normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)⁆).map
            φ.toMonoidHom =
        ((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)).map φ.toMonoidHom
      rw [map_commutator, hmap, hperf]
    · change Nat.card ((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)) = _
      rw [← card_map_of_injective (f := φ.toMonoidHom) φ.injective, hmap, hcard,
        Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK, hK₂]
  · exact Or.inr ⟨η, hη, hx, φ, hφ⟩
  · exact (false_of_field_or_graphField_E6_quot hset hK e htC ht hZ hK₂ eM htM hσ2 hσ1
      (ε := 0) (φ := φ) (by norm_num) (by rw [pow_zero, one_mul]; exact hφ)).elim
  · exact (false_of_field_or_graphField_E6_quot hset hK e htC ht hZ hK₂ eM htM hσ2 hσ1
      (ε := 1) (φ := φ) (by norm_num) (by rw [pow_one]; exact hφ)).elim

end E6

section TwistedE6


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_inner_quot_twistedE6_row_27 (hset : StandardSetting G L) {f : ℕ} {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) {σ : K₂ →+* K₂} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 K₂ σ)
    (htM : t ∈ normalizer (M : Set G)) :
    normalizerQuotMulAut eM ⟨t, htM⟩ ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.E6 K₂ σ →* _).range := by
  have hf := one_le_of_natCard_eq_two_pow hK
  have := TwistedE6Pilot.finite_of_card hK₂
  have : CharP K₂ 2 := TwistedE6Pilot.charP_two_of_card hf hK₂
  intro hin
  have hu : orderOf (TwistedE6Pilot.stdRepC (TwistedE6Pilot.apply_apply_eq hK₂ hσ) 0) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (TwistedE6Pilot.stdRep_sq 0)
    · intro h1
      have h2 := congrArg (fun z : graphFixedRootGroup TwistTag.E6 K₂ σ =>
        (z : ModGL TwistTag.E6.tag K₂)) h1
      exact CFSG.LieType.Chevalley.E6SecondGraphFixed.pinnedX_e6HighestRoot_one_ne_one h2
  obtain ⟨ŵ, hŵ, hdvd⟩ := exists_involution_card_centralizer_dvd_of_inner_quot ht hMp hZ eM htM
    hu hin
  exact not_two_pow_dvd_card_centralizer_F4_27 hset hf hK e htC ht hKt
    ((two_pow_dvd_card_centralizer_twistedE6_27 hf hK₂ hσ hŵ).trans hdvd)

theorem inf_centralizer_eq_or_xi_twistedE6_quot_27 (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) (σ : K₂ →+* K₂) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 K₂ σ)
    (htM : t ∈ normalizer (M : Set G)) :
    (M ⊓ centralizer ({t} : Set G) = L ∧
      ∃ η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
        (∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
          diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) ∧
        ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
          φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = η) ∨
      ∃ (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K₂ σ)
        (φ η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)),
        (∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
          diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) ∧
        φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η :=
  inf_centralizer_eq_or_xi_twistedE6_quot hset hK e htC ht hKt hZ hK₂ σ hσ eM htM
    (not_inner_quot_twistedE6_row_27 hset hK e htC ht hKt hMp hZ hK₂ hσ eM htM)

end TwistedE6

end CFSG.SeitzReduction.F4Pilot
