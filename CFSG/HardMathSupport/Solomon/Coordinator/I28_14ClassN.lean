module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Defs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLForm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module Submodule
  CFSG.LocalAnalysis.ComponentInitial

section
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem i28_14_N_inv_apply (g : LinearMap.GeneralLinearGroup (ZMod 2) U) (x : U) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U)
      ((g : U →ₗ[ZMod 2] U) x) = x := by
  change ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x = x
  rw [inv_mul_cancel]
  rfl

theorem i28_14_N_apply_inv (g : LinearMap.GeneralLinearGroup (ZMod 2) U) (x : U) :
    (g : U →ₗ[ZMod 2] U)
      (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x) = x := by
  change ((g * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x = x
  rw [mul_inv_cancel]
  rfl

theorem i28_14_N_apply_ne_zero (g : LinearMap.GeneralLinearGroup (ZMod 2) U) {a : U}
    (ha : a ≠ 0) : (g : U →ₗ[ZMod 2] U) a ≠ 0 := fun h => ha (by
  rw [← i28_14_N_inv_apply g a, h, map_zero])

theorem i28_14_N_dual_comp_ne_zero (g : LinearMap.GeneralLinearGroup (ZMod 2) U)
    {φ : Dual (ZMod 2) U} (hφ : φ ≠ 0) :
    φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) ≠ 0 := by
  intro h
  refine hφ (LinearMap.ext fun v => ?_)
  have := LinearMap.congr_fun h ((g : U →ₗ[ZMod 2] U) v)
  rwa [LinearMap.comp_apply, i28_14_N_inv_apply, LinearMap.zero_apply] at this

theorem i28_14_N_conj (g : LinearMap.GeneralLinearGroup (ZMod 2) U) (φ : Dual (ZMod 2) U) (a : U)
    (h : φ a = 0) : ∃ h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) :
      U →ₗ[ZMod 2] U)) ((g : U →ₗ[ZMod 2] U) a) = 0,
      g * tv φ a h * g⁻¹ = tv (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) :
        U →ₗ[ZMod 2] U)) ((g : U →ₗ[ZMod 2] U) a) h' := by
  have h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U))
      ((g : U →ₗ[ZMod 2] U) a) = 0 := by
    rw [LinearMap.comp_apply, i28_14_N_inv_apply]
    exact h
  exact ⟨h', conj_tv g φ a h h'⟩

theorem i28_14_N_alt_comm {f : LinearMap.BilinForm (ZMod 2) U} (halt : f.IsAlt) (x y : U) :
    f x y = f y x := by
  have h := halt (x + y)
  have hx := halt x
  have hy := halt y
  simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero] at h
  generalize f x y = α at h ⊢
  generalize f y x = β at h ⊢
  revert α β
  decide

theorem i28_14_N_sp_tv_mem {f : LinearMap.BilinForm (ZMod 2) U} (hnd : f.Nondegenerate)
    (halt : f.IsAlt) {φ : Dual (ZMod 2) U} {a : U} (h : φ a = 0) (hφ : φ ≠ 0) (ha : a ≠ 0)
    (hmem : tv φ a h ∈ bilinIsometryGroup f) : φ = f a := by
  obtain ⟨x₀, hx₀⟩ := exists_apply_eq_one hφ
  have haa : f a a = 0 := halt a
  have hy : ∀ y, f a y = φ y * f x₀ a := by
    intro y
    have e := hmem x₀ y
    simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hx₀, haa, one_mul, mul_zero, add_zero] at e
    generalize f x₀ y = α at e
    generalize f a y = β at e ⊢
    generalize f x₀ a = γ at e ⊢
    generalize φ y = δ at e ⊢
    revert α β γ δ
    decide
  have hc : f x₀ a = 1 := by
    rcases zmod2_eq_zero_or_one (f x₀ a) with h0 | h1
    · exfalso
      refine ha (hnd.1 a fun y => ?_)
      rw [hy y, h0, mul_zero]
    · exact h1
  exact LinearMap.ext fun y => by rw [hy y, hc, mul_one]

theorem i28_14_N_sp {f : LinearMap.BilinForm (ZMod 2) U} (hnd : f.Nondegenerate)
    (halt : f.IsAlt) {g : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (hg : ∀ x ∈ bilinIsometryGroup f, g * x * g⁻¹ ∈ bilinIsometryGroup f) :
    g ∈ bilinIsometryGroup f := by
  have key : ∀ v : U, v ≠ 0 → ∀ w, f ((g : U →ₗ[ZMod 2] U) v) ((g : U →ₗ[ZMod 2] U) w) = f v w := by
    intro v hv w
    have hcomm := i28_14_N_alt_comm halt
    have h0 : f v v = 0 := halt v
    have ht := hg _ (tv_mem_bilinIsometryGroup hcomm (a := v) h0)
    obtain ⟨h', he⟩ := i28_14_N_conj g (f v) v h0
    rw [he] at ht
    have hne : f v ≠ 0 := fun h => hv (hnd.1 v fun y => by rw [h]; rfl)
    have hφ := i28_14_N_sp_tv_mem hnd halt h' (i28_14_N_dual_comp_ne_zero g hne)
      (i28_14_N_apply_ne_zero g hv) ht
    have := LinearMap.congr_fun hφ ((g : U →ₗ[ZMod 2] U) w)
    rw [LinearMap.comp_apply, i28_14_N_inv_apply] at this
    exact this.symm
  intro v w
  by_cases hv : v = 0
  · subst hv
    simp
  · exact key v hv w

end

section
variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

set_option linter.unusedSectionVars false in
theorem tvN_sp {f : LinearMap.BilinForm (ZMod 2) U} (hnd : f.Nondegenerate) (halt : f.IsAlt)
    (hirr : IsTvIrred (bilinIsometryGroup f))
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (hg : ∀ x ∈ bilinIsometryGroup f, g * x * g⁻¹ ∈ bilinIsometryGroup f) :
    g ∈ bilinIsometryGroup f := by
  have _hirr := hirr
  exact i28_14_N_sp hnd halt hg

end

end CFSG.HardMathSupport.Solomon.Coordinator
