module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsE6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainOdd

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.Quasithin (perfectCore)

section Normalize


variable {K₂ : Type} [Field K₂] [Finite K₂]

theorem range_fixedFieldInclusion_eq_eqLocus [CharP K₂ ReeTag.F4.prime] {f : ℕ} (hf : 1 ≤ f)
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) {σ : K₂ ≃+* K₂} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (fixedFieldInclusion (τ := .F4) σ).range =
      ((ReeTag.F4.finiteExceptionalAut K₂ ^ (2 * f) : MulAut (adjointGroup .F4 K₂))).toMonoidHom.eqLocus
        (MonoidHom.id _) := by
  obtain ⟨-, -, -, -, -, hJ, -⟩ := even_F4_canonical_field_full_centralizer hf K₂ hK₂ σ hσ
  ext g
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    have hmem : ((fixedFieldInclusion (τ := .F4) σ x : adjointGroup .F4 K₂) : ModGL .F4 K₂) ∈
        fixedFieldImage ReeTag.F4.tag σ := (mem_fixedFieldImage_iff_exists σ _).2 ⟨x, rfl⟩
    rw [← hJ] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = fixedFieldInclusion σ x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro hg
    have hmem : (g : ModGL .F4 K₂) ∈ fixedFieldImage ReeTag.F4.tag σ := by
      rw [← hJ]
      exact ⟨g, hg, rfl⟩
    exact (mem_fixedFieldImage_iff_exists σ g).1 hmem

theorem exists_injective_comp_fixedFieldInclusion_eq {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}
    (hf : 1 ≤ f) (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hk : Nat.card (fixSubfield σ) = 2 ^ f) (e : L ≃* adjointGroup .F4 (fixSubfield σ)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M : Subgroup G}
    (eM : M ≃* adjointGroup .F4 K₂) (htM : t ∈ normalizer (M : Set G))
    (hML : M ⊓ centralizer ({t} : Set G) = L) :
    ∃ Φ : adjointGroup .F4 K₂ →* G, Function.Injective Φ ∧ Φ.range = M ∧
      ∀ x : adjointGroup .F4 (fixSubfield σ),
        Φ (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
  have : CharP K₂ ReeTag.F4.prime := ‹CharP K₂ 2›
  have : Finite (fixSubfield σ) := finite_of_natCard_eq_two_pow hk
  have : CharP (fixSubfield σ) ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hk
  have : Finite (ModGL .F4 (fixSubfield σ)) := finite_modGL
  set α := normalizerMulAut eM ⟨t, htM⟩ with hα
  have hα2 : α ^ 2 = 1 := normalizerMulAut_sq_eq_one eM ht htM
  have hαo : α ∉ (MulAut.conj : adjointGroup .F4 K₂ →* MulAut (adjointGroup .F4 K₂)).range :=
    fun h => not_exists_inner_F4_field hset hk e htC ht hK₂ eM
      (exists_inner_of_normalizerMulAut_mem_range eM htM h)
  obtain ⟨ψ₀, -, -, -, hfix, -⟩ :=
    even_F4_all_outer_involutions_canonical (f := 2 * f) (by omega) K₂ hK₂ α hα2 hαo
  set ψ : MulAut (adjointGroup .F4 K₂) := ψ₀ with hψ
  have hfix' : (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
      ((ReeTag.F4.finiteExceptionalAut K₂ ^ (2 * f) : MulAut (adjointGroup .F4 K₂))).toMonoidHom.eqLocus
        (MonoidHom.id _) := hfix
  have hrange := range_fixedFieldInclusion_eq_eqLocus hf hK₂ hσ
  set Φ₀ : adjointGroup .F4 K₂ →* G :=
    (M.subtype.comp eM.symm.toMonoidHom).comp ψ.symm.toMonoidHom with hΦ₀
  have hΦ₀inj : Function.Injective Φ₀ :=
    (M.subtype_injective.comp eM.symm.injective).comp ψ.symm.injective
  have hΦ₀range : Φ₀.range = M := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (eM.symm (ψ.symm y)).2
    · intro hx
      refine ⟨ψ (eM ⟨x, hx⟩), ?_⟩
      change ((eM.symm (ψ.symm (ψ (eM ⟨x, hx⟩))) : M) : G) = x
      rw [ψ.symm_apply_apply, eM.symm_apply_apply]
  have hΦ₀L : ∀ x, Φ₀ (fixedFieldInclusion σ x) ∈ L := by
    intro x
    have h1 : fixedFieldInclusion σ x ∈
        ((ReeTag.F4.finiteExceptionalAut K₂ ^ (2 * f) :
          MulAut (adjointGroup .F4 K₂))).toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    rw [← hfix'] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rw [← hML, inf_centralizer_eq_map_eqLocus eM htM]
    refine ⟨y, hy, ?_⟩
    have hy' : ψ.symm (fixedFieldInclusion σ x) = y := by
      rw [MulEquiv.symm_apply_eq]
      exact hyx.symm
    change ((eM.symm y : M) : G) = ((eM.symm (ψ.symm (fixedFieldInclusion σ x)) : M) : G)
    rw [hy']
  set β₀ : adjointGroup .F4 (fixSubfield σ) →* adjointGroup .F4 (fixSubfield σ) :=
    e.toMonoidHom.comp ((Φ₀.comp (fixedFieldInclusion σ)).codRestrict L hΦ₀L) with hβ₀
  have hβ₀inj : Function.Injective β₀ := by
    intro x y hxy
    have h1 := congrArg (fun z => ((e.symm z : L) : G)) hxy
    simp only [hβ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      MonoidHom.codRestrict_apply] at h1
    exact fixedFieldInclusion_injective σ (hΦ₀inj h1)
  set β : MulAut (adjointGroup .F4 (fixSubfield σ)) :=
    MulEquiv.ofBijective β₀ (Finite.injective_iff_bijective.1 hβ₀inj) with hβdef
  have hβ : ∀ x, ((e.symm (β x) : L) : G) = Φ₀ (fixedFieldInclusion σ x) := by
    intro x
    change ((e.symm (β₀ x) : L) : G) = _
    simp only [hβ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      MonoidHom.codRestrict_apply]
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form hf (fixSubfield σ) hk
  obtain ⟨⟨g₀, j⟩, hgj, -⟩ := hnf β
  set g : adjointGroup .F4 (fixSubfield σ) := g₀ with hg
  set φk : MulAut (adjointGroup .F4 (fixSubfield σ)) :=
    ReeTag.F4.finiteExceptionalAut (fixSubfield σ) ^ (j : ℕ) with hφk
  set φK : MulAut (adjointGroup .F4 K₂) := ReeTag.F4.finiteExceptionalAut K₂ ^ (j : ℕ) with hφK
  have hgj' : β = MulAut.conj g * φk := hgj
  set βh : MulAut (adjointGroup .F4 K₂) := MulAut.conj (fixedFieldInclusion σ g) * φK with hβh
  have hβh : ∀ x, βh (fixedFieldInclusion σ x) = fixedFieldInclusion σ (β x) := by
    intro x
    have hφ : φK (fixedFieldInclusion σ x) = fixedFieldInclusion σ (φk x) :=
      finiteExceptionalAut_pow_fixedFieldInclusion σ (j : ℕ) x
    have hβx : β x = g * φk x * g⁻¹ := by
      rw [hgj']
      rfl
    calc βh (fixedFieldInclusion σ x) =
          fixedFieldInclusion σ g * φK (fixedFieldInclusion σ x) * (fixedFieldInclusion σ g)⁻¹ :=
            rfl
      _ = fixedFieldInclusion σ g * fixedFieldInclusion σ (φk x) * (fixedFieldInclusion σ g)⁻¹ := by
            rw [hφ]
      _ = fixedFieldInclusion σ (g * φk x * g⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = fixedFieldInclusion σ (β x) := by rw [hβx]
  have hβhs : ∀ x, βh.symm (fixedFieldInclusion σ x) = fixedFieldInclusion σ (β.symm x) := by
    intro x
    apply βh.injective
    rw [MulEquiv.apply_symm_apply, hβh, MulEquiv.apply_symm_apply]
  refine ⟨Φ₀.comp βh.symm.toMonoidHom, hΦ₀inj.comp βh.symm.injective, ?_, fun x => ?_⟩
  · rw [← hΦ₀range]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨βh.symm z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨βh z, by simp⟩
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβhs]
    rw [← hβ, MulEquiv.apply_symm_apply]

theorem le_iSup_perfectCore_of_mem_normalizer_F4_field {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}
    (hf : 2 ≤ f) (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hk : Nat.card (fixSubfield σ) = 2 ^ f) (e : L ≃* adjointGroup .F4 (fixSubfield σ)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M : Subgroup G}
    (eM : M ≃* adjointGroup .F4 K₂) (htM : t ∈ normalizer (M : Set G)) :
    M ≤ ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      perfectCore (M ⊓ centralizer (modelToG e (leviTorus (fixSubfield σ) J.1) : Set G)) := by
  have hML := inf_centralizer_eq_of_mem_normalizer_F4_field hset hk e htC ht hK₂ eM htM
  obtain ⟨Φ, hΦinj, hΦrange, hΦ⟩ :=
    exists_injective_comp_fixedFieldInclusion_eq hset (by omega) hK₂ hσ hk e htC ht eM htM hML
  have hq : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h := range_le_iSup_perfectCore_modelToG_of_comp_fixedFieldInclusion hq e hΦinj hΦ
  rw [hΦrange] at h
  exact h

end Normalize

section Input


theorem fieldRowUniqueOddInput_holds : FieldRowUniqueOddInput := by
  intro G _ _ L K₂ _ _ _ σ f hq hf e t hw _ _ ψ hinj hrange _ h htM _
  let Ψ : adjointGroup .F4 K₂ ≃* pieceSpan e :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let eM : CFSG.conjugate (pieceSpan e) h ≃* adjointGroup .F4 K₂ :=
    (conjugateSymmEquiv (pieceSpan e) h).trans Ψ.symm
  have hgen := le_iSup_perfectCore_of_mem_normalizer_F4_field hw.standard hf hq.card_eq
    hq.apply_eq hw.card_eq e hw.mem_centralizer hw.orderOf_eq eM htM
  exact eq_of_le_iSup_perfectCore hgen
    (fun J => le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1) J)
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm)

end Input

end CFSG.SeitzReduction.F4Pilot
