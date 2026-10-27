module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotUniqueFieldInner
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionOuter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldFix

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open E6Pilot (fixSubgroup)

section Fix

variable {K : Type} [Field K]

theorem fixSubgroup_entrywiseAdjointAut_eq_range_E8 [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    fixSubgroup (entrywiseAdjointAut .E8 σ) = (fixedFieldInclusion σ).range := by
  obtain ⟨-, -, -, hmap, -⟩ :=
    even_E7_E8_canonical_field_full_centralizer .E8 (Or.inr rfl) he K hK σ hσ
  apply Subgroup.map_injective (adjointGroup .E8 K).subtype_injective
  change ((entrywiseAdjointAut .E8 σ).toMonoidHom.eqLocus (MonoidHom.id _)).map _ = _
  rw [hmap]
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fixedFieldInclusion σ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, y.2, rfl⟩

theorem fixSubgroup_entrywiseAdjointAut_facts_E8 [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    ⁅fixSubgroup (entrywiseAdjointAut .E8 σ), fixSubgroup (entrywiseAdjointAut .E8 σ)⁆ =
        fixSubgroup (entrywiseAdjointAut .E8 σ) ∧
      Nat.card (fixSubgroup (entrywiseAdjointAut .E8 σ)) = ordE8 (2 ^ e) := by
  obtain ⟨-, hk, -⟩ := even_E7_E8_canonical_field_full_centralizer .E8 (Or.inr rfl) he K hK σ hσ
  rw [fixSubgroup_entrywiseAdjointAut_eq_range_E8 he hK σ hσ]
  refine ⟨?_, ?_⟩
  · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      (CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 (K := fixSubfield σ)).commutator_eq_top]
  · rw [MonoidHom.range_eq_map, card_map_of_injective (fixedFieldInclusion_injective σ),
      Subgroup.card_top, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hk]

end Fix

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_field_and_inf_centralizer_eq_E8_field (hset : StandardSetting G L)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .E8 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    (∃ σ : K₂ ≃+* K₂, σ ^ 2 = 1 ∧ σ ≠ 1 ∧ (∀ c, σ c = c ^ (2 ^ f)) ∧
      ∃ ψ : M ≃* adjointGroup .E8 K₂, ∀ x : M,
        ψ (M.normalizerMonoidHom ⟨t, htM⟩ x) = entrywiseAdjointAut .E8 σ (ψ x)) ∧
    M ⊓ centralizer ({t} : Set G) = L := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨2, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).2.2⟩⟩
  have htC : t ∈ centralizer (L : Set G) := (hKt ▸ mem_zpowers t :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).1
  set X : Subgroup G := M ⊓ centralizer ({t} : Set G) with hXdef
  have hXt : X ≤ centralizer ({t} : Set G) := inf_le_right
  set β : MulAut M := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  set α : MulAut (adjointGroup .E8 K₂) := (eM.symm.trans β).trans eM with hαdef
  have hα2 : α ^ 2 = 1 := (F4Pilot.pow_two_conj_eq_one_iff eM β).2
    (E6Pilot.normalizerMonoidHom_sq_eq_one_of_orderOf ht htM)
  have hβo : β ∉ (MulAut.conj : M →* MulAut M).range := by
    rintro ⟨m, hm⟩
    refine not_exists_inner_E8_field hset hK e ht hKt hK₂ eM ⟨m, m.2, fun x hx => ?_⟩
    have h := congrArg (fun γ : MulAut M => ((γ ⟨x, hx⟩ : M) : G)) hm
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [h, hβdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hαo : α ∉ (MulAut.conj : adjointGroup .E8 K₂ →* MulAut (adjointGroup .E8 K₂)).range :=
    fun h => hβo ((F4Pilot.conj_mem_range_conj_iff eM β).1 h)
  obtain ⟨-, Θ, -, -, hker, hinv⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form
    (by omega : 1 ≤ 2 * f) K₂ hK₂ .E8 (Or.inr rfl)
  have hΘ1 : Θ α ≠ 1 := fun h1 => hαo (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨-, hσc⟩ := (hinv α hα2).resolve_left hΘ1
  have hσ : ∀ c, Θ α c = c ^ 2 ^ f := fun c => by rw [hσc, show 2 * f / 2 = f by omega]
  have hσ2 : Θ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
  obtain ⟨ψ₀, hψ₀⟩ :=
    exists_conj_eq_entrywise_of_outer_E7_E8 (Or.inr rfl) hf K₂ hK₂ (Θ α) hσ hα2 hαo
  refine ⟨⟨Θ α, hσ2, hΘ1, hσ, eM.trans ψ₀, fun x => ?_⟩, ?_⟩
  · have h := congrArg (fun γ : MulAut (adjointGroup .E8 K₂) => γ (ψ₀ (eM x))) hψ₀
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h
    have hα : α (eM x) = eM (β x) := by
      rw [hαdef, F4Pilot.conj_mulEquiv_apply, MulEquiv.symm_apply_apply]
    change ψ₀ (eM (β x)) = entrywiseAdjointAut .E8 (Θ α) (ψ₀ (eM x))
    rw [← h, hα]
  · set φM : adjointGroup .E8 K₂ →* G := M.subtype.comp eM.symm.toMonoidHom with hφM
    have hφinj : Function.Injective φM := M.subtype_injective.comp eM.symm.injective
    have hCM : X = (fixSubgroup α).map φM := E6Pilot.inf_centralizer_eq_map_fixSubgroup eM htM
    have hfix : (fixSubgroup (entrywiseAdjointAut .E8 (Θ α))).map ψ₀⁻¹.toMonoidHom =
        fixSubgroup α := by
      rw [E6Pilot.map_fixSubgroup_conj, ← hψ₀]
      congr 1
      group
    obtain ⟨hperf, hcard⟩ := fixSubgroup_entrywiseAdjointAut_facts_E8 hf hK₂ (Θ α) hσ
    have hXX : ⁅X, X⁆ = X := by
      rw [hCM, ← map_commutator, ← hfix, ← map_commutator, hperf]
    refine Subgroup.eq_of_le_of_card_ge (std_perfect_le hset hOut htC ht hXX hXt) ?_
    rw [hCM, card_map_of_injective hφinj, ← hfix, card_map_of_injective ψ₀⁻¹.injective, hcard,
      Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hK]

theorem inf_centralizer_eq_of_mem_normalizer_E8_field (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .E8 K₂)
    (htM : t ∈ normalizer (M : Set G)) : M ⊓ centralizer ({t} : Set G) = L :=
  (exists_field_and_inf_centralizer_eq_E8_field hset hK e ht hKt hK₂ eM htM).2

theorem inf_centralizer_conjugate_eq_E8_field (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ≃* adjointGroup .E8 K₂)
    (h : G) (htM : t ∈ normalizer (conjugate G₀ h : Set G)) :
    conjugate G₀ h ⊓ centralizer ({t} : Set G) = L :=
  inf_centralizer_eq_of_mem_normalizer_E8_field hset hK e ht hKt hK₂
    ((G₀.equivMapOfInjective _ (MulAut.conj h⁻¹).injective).symm.trans e₀) htM

end Standard

end CFSG.SeitzReduction.E8Pilot
