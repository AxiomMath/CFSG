module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LargeExtraspecial.DW2ModBasic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection tv tv_apply tv_ext conj_tv
  isF2Transvection_iff exists_apply_eq_one tv_mul_tv_center tv_mul_tv_axis commutatorSpace)

section Flag

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

theorem exists_linearEquiv_apply_eq_of_finrank {M M' : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] [AddCommGroup M'] [Module (ZMod 2) M'] [FiniteDimensional (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M'] (h : finrank (ZMod 2) M = finrank (ZMod 2) M') {x : M}
    {x' : M'} (hx : x ≠ 0) (hx' : x' ≠ 0) : ∃ e : M ≃ₗ[ZMod 2] M', e x = x' := by
  let e₀ : M ≃ₗ[ZMod 2] M' := LinearEquiv.ofFinrankEq M M' h
  have hy : e₀ x ≠ 0 := fun h0 => hx (e₀.injective (by simpa using h0))
  let f : (ZMod 2 ∙ e₀ x) ≃ₗ[ZMod 2] (ZMod 2 ∙ x') :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) M' (e₀ x) hy).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton (ZMod 2) M' x' hx'
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e₀ ≪≫ₗ g, ?_⟩
  have h1 := hg ⟨e₀ x, Submodule.mem_span_singleton_self _⟩
  have h2 : f ⟨e₀ x, Submodule.mem_span_singleton_self _⟩ =
      ⟨x', Submodule.mem_span_singleton_self _⟩ := by
    have e1 : (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) M' (e₀ x) hy).symm
        ⟨e₀ x, Submodule.mem_span_singleton_self _⟩ = 1 := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      simp
    simp only [f, LinearEquiv.trans_apply, e1]
    apply Subtype.ext
    simp
  rw [h2] at h1
  exact h1.symm

theorem finrank_ker_add_one {φ : Dual (ZMod 2) E} (hφ : φ ≠ 0) :
    finrank (ZMod 2) (LinearMap.ker φ) + 1 = finrank (ZMod 2) E := by
  have hr : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    obtain ⟨u, hu⟩ := exists_apply_eq_one hφ
    exact ⟨c • u, by rw [map_smul, hu, smul_eq_mul, mul_one]⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  rw [hr, finrank_top, Module.finrank_self] at h1
  omega

theorem exists_flag_linearEquiv {φ φ' : Dual (ZMod 2) E} {a a' : E} (hφ : φ ≠ 0)
    (hφ' : φ' ≠ 0) (ha : a ≠ 0) (ha' : a' ≠ 0) (h : φ a = 0) (h' : φ' a' = 0) :
    ∃ g : E ≃ₗ[ZMod 2] E, g a = a' ∧ ∀ v, φ' (g v) = φ v := by
  obtain ⟨u, hu⟩ := exists_apply_eq_one hφ
  obtain ⟨u', hu'⟩ := exists_apply_eq_one hφ'
  set K := LinearMap.ker φ
  set K' := LinearMap.ker φ'
  have hK : finrank (ZMod 2) K = finrank (ZMod 2) K' := by
    have h1 : finrank (ZMod 2) K + 1 = finrank (ZMod 2) E := finrank_ker_add_one hφ
    have h2 : finrank (ZMod 2) K' + 1 = finrank (ZMod 2) E := finrank_ker_add_one hφ'
    omega
  obtain ⟨e, he⟩ := exists_linearEquiv_apply_eq_of_finrank hK (x := ⟨a, h⟩) (x' := ⟨a', h'⟩)
    (fun h0 => ha (congrArg Subtype.val h0)) (fun h0 => ha' (congrArg Subtype.val h0))
  let P : E →ₗ[ZMod 2] K := LinearMap.codRestrict K (LinearMap.id - φ.smulRight u) fun v => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
      LinearMap.smulRight_apply, map_smul, hu, smul_eq_mul, mul_one, sub_self]
  let P' : E →ₗ[ZMod 2] K' := LinearMap.codRestrict K' (LinearMap.id - φ'.smulRight u') fun v => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
      LinearMap.smulRight_apply, map_smul, hu', smul_eq_mul, mul_one, sub_self]
  have hP : ∀ v, (P v : E) = v - φ v • u := fun v => rfl
  have hP' : ∀ v, (P' v : E) = v - φ' v • u' := fun v => rfl
  let g₁ : E →ₗ[ZMod 2] E := K'.subtype ∘ₗ (e : K →ₗ[ZMod 2] K') ∘ₗ P + φ.smulRight u'
  let g₂ : E →ₗ[ZMod 2] E := K.subtype ∘ₗ (e.symm : K' →ₗ[ZMod 2] K) ∘ₗ P' + φ'.smulRight u
  have hg₁ : ∀ v, g₁ v = (e (P v) : E) + φ v • u' := fun v => rfl
  have hg₂ : ∀ v, g₂ v = (e.symm (P' v) : E) + φ' v • u := fun v => rfl
  have hφg₁ : ∀ v, φ' (g₁ v) = φ v := by
    intro v
    rw [hg₁, map_add, map_smul, hu', smul_eq_mul, mul_one, (e (P v)).2, zero_add]
  have hφg₂ : ∀ v, φ (g₂ v) = φ' v := by
    intro v
    rw [hg₂, map_add, map_smul, hu, smul_eq_mul, mul_one, (e.symm (P' v)).2, zero_add]
  have h12 : ∀ v, g₁ (g₂ v) = v := by
    intro v
    rw [hg₁, hφg₂]
    have : P (g₂ v) = e.symm (P' v) := by
      apply Subtype.ext
      rw [hP, hφg₂, hg₂, add_sub_cancel_right]
    rw [this, LinearEquiv.apply_symm_apply, hP']
    abel
  have h21 : ∀ v, g₂ (g₁ v) = v := by
    intro v
    rw [hg₂, hφg₁]
    have : P' (g₁ v) = e (P v) := by
      apply Subtype.ext
      rw [hP', hφg₁, hg₁, add_sub_cancel_right]
    rw [this, LinearEquiv.symm_apply_apply, hP]
    abel
  refine ⟨LinearEquiv.ofLinearMap g₁ g₂ (LinearMap.ext h12) (LinearMap.ext h21), ?_, hφg₁⟩
  change g₁ a = a'
  rw [hg₁, h, zero_smul, add_zero]
  have : P a = ⟨a, h⟩ := by
    apply Subtype.ext
    rw [hP, h, zero_smul, sub_zero]
  rw [this, he]

theorem exists_conj_of_isF2Transvection {τ τ' : LinearMap.GeneralLinearGroup (ZMod 2) E}
    (hτ : IsF2Transvection τ) (hτ' : IsF2Transvection τ') :
    ∃ g : LinearMap.GeneralLinearGroup (ZMod 2) E, τ' = g * τ * g⁻¹ := by
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff τ).mp hτ
  obtain ⟨φ', a', h', hφ', ha', rfl⟩ := (isF2Transvection_iff τ').mp hτ'
  obtain ⟨g, hga, hgφ⟩ := exists_flag_linearEquiv hφ hφ' ha ha' h h'
  refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv g, tv_ext fun v => ?_⟩
  change v + φ' v • a' = (g : E →ₗ[ZMod 2] E) (((tv φ a h : LinearMap.GeneralLinearGroup
    (ZMod 2) E) : E →ₗ[ZMod 2] E) (g.symm v))
  rw [tv_apply]
  change v + φ' v • a' = g (g.symm v + φ (g.symm v) • a)
  rw [map_add, map_smul, LinearEquiv.apply_symm_apply, hga, ← hgφ, LinearEquiv.apply_symm_apply]

theorem eq_of_finrank_le_one' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {U : Submodule (ZMod 2) M} [FiniteDimensional (ZMod 2) U] (hU : finrank (ZMod 2) U ≤ 1)
    {v v' : M} (hv : v ∈ U) (hv' : v' ∈ U) (hv0 : v ≠ 0) (hv'0 : v' ≠ 0) : v = v' := by
  have hspan : ZMod 2 ∙ v = U := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hv
    · rw [finrank_span_singleton hv0]
      exact hU
  rw [← hspan] at hv'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv'
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul] at hv'0
    exact absurd rfl hv'0
  · rw [one_smul]

end Flag

end CFSG.LargeExtraspecial.DW
