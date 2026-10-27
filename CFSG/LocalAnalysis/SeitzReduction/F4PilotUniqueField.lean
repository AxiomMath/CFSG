module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueFieldInner
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.OuterAutomorphisms

theorem commutator_eq_top_of_isSimpleGroup_of_four_dvd {S : Type*} [Group S]
    (hS : IsSimpleGroup S) (h4 : 4 ∣ Nat.card S) : _root_.commutator S = ⊤ := by
  rcases hS.eq_bot_or_eq_top_of_normal (_root_.commutator S) with h | h
  · have : IsMulCommutative S := (commutator_eq_bot_iff (G := S)).1 h
    have hp := (Group.is_simple_iff_prime_card (α := S)).1 hS
    rcases hp.eq_one_or_self_of_dvd 2 (dvd_trans (by norm_num) h4) with h2 | h2
    · omega
    · rw [← h2] at h4
      omega
  · exact h

theorem four_dvd_ordF4_two_pow {f : ℕ} (hf : 1 ≤ f) : 4 ∣ CFSG.Open.ordF4 (2 ^ f) := by
  have h : 4 ∣ (2 ^ f) ^ 24 := by
    rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  unfold CFSG.Open.ordF4
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left h _) _) _) _

theorem eqLocus_perfect_card_of_outer_F4 {f : ℕ} {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (α : MulAut (adjointGroup .F4 K₂)) (hα : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup .F4 K₂ →* MulAut (adjointGroup .F4 K₂)).range) :
    ⁅α.toMonoidHom.eqLocus (MonoidHom.id _), α.toMonoidHom.eqLocus (MonoidHom.id _)⁆ =
        α.toMonoidHom.eqLocus (MonoidHom.id _) ∧
      Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id _)) = CFSG.Open.ordF4 (2 ^ f) := by
  have := finite_of_natCard_eq_two_pow hK₂
  have hc := charP_two_of_natCard_eq_two_pow hK₂
  have : CharP K₂ ReeTag.F4.prime := hc
  have hf1 : 1 ≤ f := by have := one_le_of_natCard_eq_two_pow hK₂; omega
  obtain ⟨ψ, -, -, -, hfix, -⟩ :=
    even_F4_all_outer_involutions_canonical (f := 2 * f) (by omega) K₂ hK₂ α hα hαo
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * f) hK₂
  have hσ : ∀ c, (fr ^ f) c = c ^ 2 ^ f := ringAut_pow_apply_of_frobenius hfr f
  obtain ⟨-, -, -, -, -, hJ, ⟨-, hJsimple, -, hJmodel⟩, -⟩ :=
    even_F4_canonical_field_full_centralizer hf1 K₂ hK₂ (fr ^ f) hσ
  let ψ' : MulAut (adjointGroup .F4 K₂) := ψ
  let η : MulAut (adjointGroup .F4 K₂) := ReeTag.F4.finiteExceptionalAut K₂ ^ (2 * f)
  have hfix' : (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ'.toMonoidHom =
      η.toMonoidHom.eqLocus (MonoidHom.id _) := hfix
  have hJ' : (η.toMonoidHom.eqLocus (MonoidHom.id _)).map (adjointGroup .F4 K₂).subtype =
      fixedFieldImage .F4 (fr ^ f) := hJ
  have hJmodel' : ChevalleyExceptionalModel (fixedFieldImage .F4 (fr ^ f)) .F4 2 f := hJmodel
  have hJsimple' : IsSimpleGroup (fixedFieldImage .F4 (fr ^ f)) := hJsimple
  have hJcard : Nat.card (fixedFieldImage .F4 (fr ^ f)) = CFSG.Open.ordF4 (2 ^ f) :=
    CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hJmodel'.2
  have hJperf := commutator_eq_top_of_isSimpleGroup_of_four_dvd hJsimple'
    (hJcard ▸ four_dvd_ordF4_two_pow hf1)
  have hJJ : ⁅fixedFieldImage .F4 (fr ^ f), fixedFieldImage .F4 (fr ^ f)⁆ =
      fixedFieldImage .F4 (fr ^ f) := by
    rw [← Subgroup.map_subtype_commutator, hJperf, ← MonoidHom.range_eq_map, range_subtype]
  have hAA : ⁅η.toMonoidHom.eqLocus (MonoidHom.id _), η.toMonoidHom.eqLocus (MonoidHom.id _)⁆ =
      η.toMonoidHom.eqLocus (MonoidHom.id _) := by
    apply Subgroup.map_injective (adjointGroup .F4 K₂).subtype_injective
    rw [map_commutator, hJ', hJJ]
  refine ⟨?_, ?_⟩
  · apply Subgroup.map_injective (f := ψ'.toMonoidHom) ψ'.injective
    rw [map_commutator, hfix', hAA]
  · rw [← Subgroup.card_map_of_injective (f := ψ'.toMonoidHom) ψ'.injective, hfix',
      ← Subgroup.card_map_of_injective (adjointGroup .F4 K₂).subtype_injective, hJ', hJcard]

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem normalizerMonoidHom_not_mem_range_conj_F4_field (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .F4 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    M.normalizerMonoidHom ⟨t, htM⟩ ∉ (MulAut.conj : M →* MulAut M).range := by
  rintro ⟨m, hm⟩
  refine not_exists_inner_F4_field hset hK e htC ht hK₂ eM ⟨m, m.2, fun x hx => ?_⟩
  have h := congrArg (fun γ : MulAut M => ((γ ⟨x, hx⟩ : M) : G)) hm
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [h, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem inf_centralizer_eq_of_mem_normalizer_F4_field (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ≃* adjointGroup .F4 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    M ⊓ centralizer ({t} : Set G) = L := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨5, derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_ordinary_small_rank_Schreier .F4 K).2 (Or.inl rfl))⟩⟩
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set β : MulAut M := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  set α : MulAut (adjointGroup .F4 K₂) := (eM.symm.trans β).trans eM with hαdef
  have hβ2 : β ^ 2 = 1 := by
    refine MulEquiv.ext fun m => Subtype.ext ?_
    rw [sq, MulAut.mul_apply, MulAut.one_apply, hβ, hβ]
    calc t * (t * (m : G) * t⁻¹) * t⁻¹ = (t * t) * m * (t * t)⁻¹ := by group
      _ = m := by rw [ht2, one_mul, inv_one, mul_one]
  have hβo : β ∉ (MulAut.conj : M →* MulAut M).range :=
    normalizerMonoidHom_not_mem_range_conj_F4_field hset hK e htC ht hK₂ eM htM
  have hαo : α ∉ (MulAut.conj : adjointGroup .F4 K₂ →* MulAut (adjointGroup .F4 K₂)).range :=
    fun h => hβo ((conj_mem_range_conj_iff eM β).1 h)
  obtain ⟨hBB, hBcard⟩ :=
    eqLocus_perfect_card_of_outer_F4 hK₂ α ((pow_two_conj_eq_one_iff eM β).2 hβ2) hαo
  set φ : adjointGroup .F4 K₂ →* G := M.subtype.comp eM.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := M.subtype_injective.comp eM.symm.injective
  have hP : M ⊓ centralizer ({t} : Set G) = (α.toMonoidHom.eqLocus (MonoidHom.id _)).map φ := by
    ext x
    constructor
    · rintro ⟨hxM, hxt⟩
      refine ⟨eM ⟨x, hxM⟩, ?_, by simp [hφ]⟩
      change α (eM ⟨x, hxM⟩) = eM ⟨x, hxM⟩
      rw [hαdef, conj_mulEquiv_apply, MulEquiv.symm_apply_apply]
      congr 1
      refine Subtype.ext ?_
      rw [hβ]
      have hxt' := mem_centralizer_singleton_iff.1 hxt
      change t * x * t⁻¹ = x
      calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [hxt']
        _ = x := by group
    · rintro ⟨b, hb, rfl⟩
      have hb' : α b = b := hb
      rw [hαdef, conj_mulEquiv_apply] at hb'
      have hb'' : β (eM.symm b) = eM.symm b := by
        have h1 := congrArg eM.symm hb'
        rwa [MulEquiv.symm_apply_apply] at h1
      have h2 := congrArg Subtype.val hb''
      rw [hβ] at h2
      refine Subgroup.mem_inf.2 ⟨(eM.symm b).2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      change ((eM.symm b : M) : G) * t = t * (eM.symm b : M)
      calc ((eM.symm b : M) : G) * t = t * (eM.symm b : M) * t⁻¹ * t := by rw [h2]
        _ = t * (eM.symm b : M) := by group
  have hperf : ⁅M ⊓ centralizer ({t} : Set G), M ⊓ centralizer ({t} : Set G)⁆ =
      M ⊓ centralizer ({t} : Set G) := by
    rw [hP, ← map_commutator, hBB]
  have hle : M ⊓ centralizer ({t} : Set G) ≤ L := std_perfect_le hset hOut htC ht hperf inf_le_right
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hP, Subgroup.card_map_of_injective hφinj, hBcard, Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK]

theorem inf_centralizer_conjugate_eq_F4_field (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {G₀ : Subgroup G}
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ≃* adjointGroup .F4 K₂)
    (h : G) (htM : t ∈ normalizer (conjugate G₀ h : Set G)) :
    conjugate G₀ h ⊓ centralizer ({t} : Set G) = L :=
  inf_centralizer_eq_of_mem_normalizer_F4_field hset hK e htC ht hK₂
    ((G₀.equivMapOfInjective _ (MulAut.conj h⁻¹).injective).symm.trans e₀) htM

end Standard

end CFSG.SeitzReduction.F4Pilot
