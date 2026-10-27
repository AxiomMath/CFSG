module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module

section Conj

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem i28_14_C_exists_apply_pair {ψ₁ ψ₂ : Dual (ZMod 2) U} (h₁ : ψ₁ ≠ 0) (h₂ : ψ₂ ≠ 0) :
    ∃ u, ψ₁ u = 1 ∧ ψ₂ u = 1 := by
  obtain ⟨x, hx⟩ := exists_apply_eq_one h₁
  obtain ⟨z, hz⟩ := exists_apply_eq_one h₂
  rcases zmod2_eq_zero_or_one (ψ₂ x) with h | h
  · rcases zmod2_eq_zero_or_one (ψ₁ z) with h' | h'
    · refine ⟨x + z, ?_, ?_⟩
      · rw [map_add, hx, h', add_zero]
      · rw [map_add, hz, h, zero_add]
    · exact ⟨z, h', hz⟩
  · exact ⟨x, hx, h⟩

theorem i28_14_C_exists_dual_eq_one {a : U} (ha : a ≠ 0) : ∃ φ : Dual (ZMod 2) U, φ a = 1 := by
  obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := (⊥ : Submodule (ZMod 2) U))
    (x := a) (by simpa using ha) inferInstance
  rcases zmod2_eq_zero_or_one (f a) with h | h
  · exact absurd h hf
  · exact ⟨f, h⟩

theorem i28_14_C_exists_dual_pair {a b : U} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ φ : Dual (ZMod 2) U, φ a = 1 ∧ φ b = 1 := by
  obtain ⟨φ₁, h₁⟩ := i28_14_C_exists_dual_eq_one ha
  obtain ⟨φ₂, h₂⟩ := i28_14_C_exists_dual_eq_one hb
  rcases zmod2_eq_zero_or_one (φ₁ b) with h | h
  · rcases zmod2_eq_zero_or_one (φ₂ a) with h' | h'
    · refine ⟨φ₁ + φ₂, ?_, ?_⟩
      · rw [LinearMap.add_apply, h₁, h', add_zero]
      · rw [LinearMap.add_apply, h₂, h, zero_add]
    · exact ⟨φ₂, h', h₂⟩
  · exact ⟨φ₁, h₁, h⟩

theorem i28_14_C_tv_congr {φ φ' : Dual (ZMod 2) U} {a a' : U} (h : φ a = 0) (h' : φ' a' = 0)
    (hφ : φ = φ') (ha : a = a') : tv φ a h = tv φ' a' h' := by
  subst hφ ha
  rfl

theorem i28_14_C_comm_tv {φ : Dual (ZMod 2) U} {c : U} (h : φ c = 0)
    {e : LinearMap.GeneralLinearGroup (ZMod 2) U} (hec : (e : U →ₗ[ZMod 2] U) c = c)
    (hφ : ∀ x, φ ((e : U →ₗ[ZMod 2] U) x) = φ x) : e * tv φ c h = tv φ c h * e := by
  refine tv_ext fun x => ?_
  change (e : U →ₗ[ZMod 2] U) ((tv φ c h : U →ₗ[ZMod 2] U) x) =
    (tv φ c h : U →ₗ[ZMod 2] U) ((e : U →ₗ[ZMod 2] U) x)
  rw [tv_apply, tv_apply, map_add, map_smul, hec, hφ]

theorem i28_14_C_inv_apply (g : LinearMap.GeneralLinearGroup (ZMod 2) U) (x : U) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U)
      ((g : U →ₗ[ZMod 2] U) x) = x := by
  change ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x = x
  rw [inv_mul_cancel]
  rfl

theorem i28_14_C_apply_inv (g : LinearMap.GeneralLinearGroup (ZMod 2) U) (x : U) :
    (g : U →ₗ[ZMod 2] U)
      (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x) = x := by
  change ((g * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x = x
  rw [mul_inv_cancel]
  rfl

theorem i28_14_C_exists_apply_eq {a a' : U} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    ∃ g : LinearMap.GeneralLinearGroup (ZMod 2) U, (g : U →ₗ[ZMod 2] U) a = a' := by
  by_cases h : a = a'
  · exact ⟨1, by simp [h]⟩
  · obtain ⟨φ, h1, h2⟩ := i28_14_C_exists_dual_pair ha ha'
    have hφ : φ (a + a') = 0 := by rw [map_add, h1, h2]; exact zmod2_scalar_add_self 1
    refine ⟨tv φ (a + a') hφ, ?_⟩
    rw [tv_apply, h1, one_smul, ← add_assoc, zmod2_add_self, zero_add]

theorem i28_14_C_exists_stab {φ₁ φ' : Dual (ZMod 2) U} {a' : U} (h₁ : φ₁ ≠ 0) (h' : φ' ≠ 0)
    (h₁a : φ₁ a' = 0) (h'a : φ' a' = 0) :
    ∃ g : LinearMap.GeneralLinearGroup (ZMod 2) U, (g : U →ₗ[ZMod 2] U) a' = a' ∧
      φ₁ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) = φ' := by
  obtain ⟨b, hb₁, hb'⟩ := i28_14_C_exists_apply_pair h₁ h'
  have hψb : (φ₁ + φ') b = 0 := by
    rw [LinearMap.add_apply, hb₁, hb']; exact zmod2_scalar_add_self 1
  refine ⟨tv (φ₁ + φ') b hψb, ?_, ?_⟩
  · rw [tv_apply, LinearMap.add_apply, h₁a, h'a, add_zero, zero_smul, add_zero]
  · rw [tv_inv]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, tv_apply, map_add, map_smul, hb₁, LinearMap.add_apply, smul_eq_mul,
      mul_one, ← add_assoc, zmod2_scalar_add_self, zero_add]

theorem i28_14_C_exists_conj_tv {φ φ' : Dual (ZMod 2) U} {a a' : U} (h : φ a = 0)
    (h' : φ' a' = 0) (hφ : φ ≠ 0) (ha : a ≠ 0) (hφ' : φ' ≠ 0) (ha' : a' ≠ 0) :
    ∃ g : LinearMap.GeneralLinearGroup (ZMod 2) U, g * tv φ a h * g⁻¹ = tv φ' a' h' := by
  obtain ⟨g₁, hg₁⟩ := i28_14_C_exists_apply_eq ha ha'
  set φ₁ : Dual (ZMod 2) U :=
    φ ∘ₗ ((g₁⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) with hφ₁def
  have hφ₁ : φ₁ ≠ 0 := by
    intro h0
    refine hφ (LinearMap.ext fun v => ?_)
    have := LinearMap.congr_fun h0 ((g₁ : U →ₗ[ZMod 2] U) v)
    rwa [hφ₁def, LinearMap.comp_apply, i28_14_C_inv_apply, LinearMap.zero_apply] at this
  have h₁ : φ₁ ((g₁ : U →ₗ[ZMod 2] U) a) = 0 := by
    rw [hφ₁def, LinearMap.comp_apply, i28_14_C_inv_apply]; exact h
  have hh₁ : φ₁ a' = 0 := hg₁ ▸ h₁
  obtain ⟨g₂, hg₂, hg₂'⟩ := i28_14_C_exists_stab hφ₁ hφ' hh₁ h'
  have h₂ : (φ₁ ∘ₗ ((g₂⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U))
      ((g₂ : U →ₗ[ZMod 2] U) a') = 0 := by
    rw [LinearMap.comp_apply, i28_14_C_inv_apply]; exact hh₁
  have step1 : g₁ * tv φ a h * g₁⁻¹ = tv φ₁ a' hh₁ :=
    (conj_tv g₁ φ a h h₁).trans (i28_14_C_tv_congr _ _ rfl hg₁)
  have step2 : g₂ * tv φ₁ a' hh₁ * g₂⁻¹ = tv φ' a' h' :=
    (conj_tv g₂ φ₁ a' hh₁ h₂).trans (i28_14_C_tv_congr _ _ hg₂' hg₂)
  refine ⟨g₂ * g₁, ?_⟩
  calc g₂ * g₁ * tv φ a h * (g₂ * g₁)⁻¹ = g₂ * (g₁ * tv φ a h * g₁⁻¹) * g₂⁻¹ := by group
    _ = tv φ' a' h' := by rw [step1, step2]

end Conj

end CFSG.HardMathSupport.Solomon.Coordinator
