module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.ComponentClassification.OutcomeLocal Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem tv_mul_tv_apply {φ ψ : Dual (ZMod 2) V} {a c : V} (h : φ a = 0) (h' : ψ c = 0) (v : V) :
    ((tv φ a h * tv ψ c h' : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v =
      v + ψ v • c + (φ v + ψ v * φ c) • a := by
  change (tv φ a h : V →ₗ[ZMod 2] V) ((tv ψ c h' : V →ₗ[ZMod 2] V) v) = _
  rw [tv_apply, tv_apply, map_add, map_smul, smul_eq_mul, add_smul]

theorem tv_mul_comm_of_apply_eq_zero {φ ψ : Dual (ZMod 2) V} {a c : V} (h : φ a = 0)
    (h' : ψ c = 0) (h1 : φ c = 0) (h2 : ψ a = 0) : tv φ a h * tv ψ c h' = tv ψ c h' * tv φ a h := by
  refine tv_ext fun v => ?_
  rw [tv_mul_tv_apply h h' v, tv_mul_tv_apply h' h v, h1, h2]
  simp only [mul_zero, add_zero]
  abel

theorem tv_mul_comm_iff {φ ψ : Dual (ZMod 2) V} {a c : V} (h : φ a = 0) (h' : ψ c = 0)
    (hφ : φ ≠ 0) (hψ : ψ ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0) :
    tv φ a h * tv ψ c h' = tv ψ c h' * tv φ a h ↔ (φ = ψ ∧ a = c) ∨ (φ c = 0 ∧ ψ a = 0) := by
  have key : (tv φ a h * tv ψ c h' = tv ψ c h' * tv φ a h) →
      ∀ v : V, (ψ v * φ c) • a = (φ v * ψ a) • c := by
    intro hcomm v
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V) v) hcomm
    simp only [tv_mul_tv_apply, add_smul] at h1
    refine add_left_cancel (a := v + ψ v • c + φ v • a) ?_
    calc v + ψ v • c + φ v • a + (ψ v * φ c) • a
        = v + ψ v • c + (φ v • a + (ψ v * φ c) • a) := by rw [add_assoc (v + ψ v • c)]
      _ = v + φ v • a + (ψ v • c + (φ v * ψ a) • c) := h1
      _ = v + ψ v • c + φ v • a + (φ v * ψ a) • c := by abel
  constructor
  · intro hcomm
    have hk := key hcomm
    rcases zmod2_eq_zero_or_one (φ c) with h1 | h1 <;> rcases zmod2_eq_zero_or_one (ψ a) with h2 | h2
    · exact Or.inr ⟨h1, h2⟩
    · exfalso
      obtain ⟨v, hv⟩ := exists_apply_eq_one hφ
      have := hk v
      rw [h1, h2, hv] at this
      simp at this
      exact hc this.symm
    · exfalso
      obtain ⟨v, hv⟩ := exists_apply_eq_one hψ
      have := hk v
      rw [h1, h2, hv] at this
      simp at this
      exact ha this
    · left
      obtain ⟨v, hv⟩ := exists_apply_eq_one hψ
      have hac : a = c := by
        have := hk v
        rw [h1, h2, hv] at this
        rcases zmod2_eq_zero_or_one (φ v) with h3 | h3
        · rw [h3] at this
          simp at this
          exact absurd this ha
        · rw [h3] at this
          simpa using this
      subst hac
      refine ⟨LinearMap.ext fun w => ?_, rfl⟩
      have := hk w
      rw [h1, h2] at this
      rcases zmod2_eq_zero_or_one (φ w) with h3 | h3 <;>
        rcases zmod2_eq_zero_or_one (ψ w) with h4 | h4
      · rw [h3, h4]
      · rw [h3, h4] at this
        simp at this
        exact absurd this ha
      · rw [h3, h4] at this
        simp at this
        exact absurd this.symm ha
      · rw [h3, h4]
  · rintro (⟨rfl, rfl⟩ | ⟨h1, h2⟩)
    · rfl
    · exact tv_mul_comm_of_apply_eq_zero h h' h1 h2

theorem tv_mul_tv_sq {φ ψ : Dual (ZMod 2) V} {a c : V} (h : φ a = 0) (h' : ψ c = 0)
    (hφc : φ c = 1) (hψa : ψ a = 0) :
    (tv φ a h * tv ψ c h') * (tv φ a h * tv ψ c h') = tv ψ a hψa := by
  refine tv_ext fun v => ?_
  change ((tv φ a h * tv ψ c h' : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
    (((tv φ a h * tv ψ c h' : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) = _
  rw [tv_mul_tv_apply h h' v]
  rw [tv_mul_tv_apply h h' (v + ψ v • c + (φ v + ψ v * φ c) • a)]
  rw [tv_apply]
  simp only [map_add, map_smul, smul_eq_mul, hφc, h, h', hψa, mul_zero, mul_one, add_zero,
    add_smul]
  have hX : ψ v • c + ψ v • c = 0 := zmod2_add_self _
  have hP : φ v • a + φ v • a = 0 := zmod2_add_self _
  have hQ : ψ v • a + ψ v • a = 0 := zmod2_add_self _
  calc v + ψ v • c + (φ v • a + ψ v • a) + ψ v • c + (φ v • a + ψ v • a + ψ v • a)
      = v + ψ v • a + (ψ v • c + ψ v • c) + (φ v • a + φ v • a) + (ψ v • a + ψ v • a) := by abel
    _ = v + ψ v • a := by rw [hX, hP, hQ]; abel

theorem tv_mul_tv_mul_tv {φ ψ : Dual (ZMod 2) V} {a c : V} (h : φ a = 0) (h' : ψ c = 0)
    (hφc : φ c = 1) (hψa : ψ a = 1) (h'' : (ψ + φ) (c + a) = 0) :
    tv φ a h * tv ψ c h' * tv φ a h = tv (ψ + φ) (c + a) h'' := by
  refine tv_ext fun v => ?_
  change (tv φ a h : V →ₗ[ZMod 2] V) ((tv ψ c h' : V →ₗ[ZMod 2] V)
    ((tv φ a h : V →ₗ[ZMod 2] V) v)) = _
  rw [tv_apply, tv_apply, tv_apply, tv_apply]
  simp only [map_add, map_smul, smul_eq_mul, LinearMap.add_apply, h, hφc, hψa, mul_zero,
    mul_one, add_zero, add_smul, smul_add]
  have hP : φ v • a + φ v • a = 0 := zmod2_add_self _
  calc v + φ v • a + (ψ v • c + φ v • c) + (φ v • a + (ψ v • a + φ v • a))
      = v + (ψ v • c + φ v • c + (ψ v • a + φ v • a)) + (φ v • a + φ v • a) := by abel
    _ = _ := by rw [hP, add_zero]

@[expose] def IsTv (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (φ : Dual (ZMod 2) V) (a : V) :
    Prop :=
  ∃ h : φ a = 0, g = tv φ a h

theorem IsTv.apply_eq_zero {g : LinearMap.GeneralLinearGroup (ZMod 2) V} {φ : Dual (ZMod 2) V}
    {a : V} (hg : IsTv g φ a) : φ a = 0 :=
  hg.1

theorem IsTv.mul_self {g : LinearMap.GeneralLinearGroup (ZMod 2) V} {φ : Dual (ZMod 2) V} {a : V}
    (hg : IsTv g φ a) : g * g = 1 := by
  obtain ⟨h, rfl⟩ := hg
  exact tv_mul_self φ a h

theorem IsTv.unique {g : LinearMap.GeneralLinearGroup (ZMod 2) V} {φ ψ : Dual (ZMod 2) V}
    {a b : V} (hg : IsTv g φ a) (hg' : IsTv g ψ b) (hφ : φ ≠ 0) (ha : a ≠ 0) :
    φ = ψ ∧ a = b := by
  obtain ⟨h, rfl⟩ := hg
  obtain ⟨h', hh⟩ := hg'
  exact (tv_eq_tv_iff h h' hφ ha).1 hh

theorem IsTv.comm_iff {g g' : LinearMap.GeneralLinearGroup (ZMod 2) V} {φ ψ : Dual (ZMod 2) V}
    {a c : V} (hg : IsTv g φ a) (hg' : IsTv g' ψ c) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) (ha : a ≠ 0)
    (hc : c ≠ 0) :
    g * g' = g' * g ↔ (φ = ψ ∧ a = c) ∨ (φ c = 0 ∧ ψ a = 0) := by
  obtain ⟨h, rfl⟩ := hg
  obtain ⟨h', rfl⟩ := hg'
  exact tv_mul_comm_iff h h' hφ hψ ha hc

theorem IsTv.comm_of_apply_eq_zero {g g' : LinearMap.GeneralLinearGroup (ZMod 2) V}
    {φ ψ : Dual (ZMod 2) V} {a c : V} (hg : IsTv g φ a) (hg' : IsTv g' ψ c) (h1 : φ c = 0)
    (h2 : ψ a = 0) : g * g' = g' * g := by
  obtain ⟨h, rfl⟩ := hg
  obtain ⟨h', rfl⟩ := hg'
  exact tv_mul_comm_of_apply_eq_zero h h' h1 h2

theorem IsTv.pow_four_of_dihedral {g g' : LinearMap.GeneralLinearGroup (ZMod 2) V}
    {φ ψ : Dual (ZMod 2) V} {a c : V} (hg : IsTv g φ a) (hg' : IsTv g' ψ c) (hφc : φ c = 1)
    (hψa : ψ a = 0) : (g * g') ^ 4 = 1 := by
  obtain ⟨h, rfl⟩ := hg
  obtain ⟨h', rfl⟩ := hg'
  have h4 : (tv φ a h * tv ψ c h') ^ 4 = ((tv φ a h * tv ψ c h') * (tv φ a h * tv ψ c h')) *
      ((tv φ a h * tv ψ c h') * (tv φ a h * tv ψ c h')) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4, tv_mul_tv_sq h h' hφc hψa, tv_mul_self]

theorem IsTv.conj_dihedral {g g' : LinearMap.GeneralLinearGroup (ZMod 2) V}
    {φ ψ : Dual (ZMod 2) V} {a c : V} (hg : IsTv g φ a) (hg' : IsTv g' ψ c) (hφc : φ c = 1)
    (hψa : ψ a = 1) : IsTv (g * g' * g) (ψ + φ) (c + a) := by
  obtain ⟨h, rfl⟩ := hg
  obtain ⟨h', rfl⟩ := hg'
  have h'' : (ψ + φ) (c + a) = 0 := by
    simp only [LinearMap.add_apply, map_add, h, h', hφc, hψa]
    decide
  exact ⟨h'', tv_mul_tv_mul_tv h h' hφc hψa h''⟩

theorem exists_isTv_of_isF2Transvection {t : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ht : IsF2Transvection t) : ∃ (φ : Dual (ZMod 2) V) (a : V), φ ≠ 0 ∧ a ≠ 0 ∧ IsTv t φ a := by
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).1 ht
  exact ⟨φ, a, hφ, ha, h, rfl⟩

theorem isF2Transvection_conj {t : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ht : IsF2Transvection t) (g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    IsF2Transvection (g * t * g⁻¹) := by
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).1 ht
  have h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V))
      ((g : V →ₗ[ZMod 2] V) a) = 0 := by
    rw [LinearMap.comp_apply]
    change φ (((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) a) = 0
    rw [inv_mul_cancel]
    exact h
  rw [conj_tv g φ a h h']
  refine (isF2Transvection_iff _).2 ⟨_, _, h', ?_, ?_, rfl⟩
  · intro h0
    apply hφ
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 ((g : V →ₗ[ZMod 2] V) v)
    rw [LinearMap.comp_apply] at this
    change φ (((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) = _ at this
    rw [inv_mul_cancel] at this
    exact this
  · intro h0
    apply ha
    have h1 : ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) a =
        ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          ((g : V →ₗ[ZMod 2] V) a) := rfl
    rw [inv_mul_cancel, h0, map_zero] at h1
    exact h1

end CFSG.CGT.PushingUpLit.CGT6
