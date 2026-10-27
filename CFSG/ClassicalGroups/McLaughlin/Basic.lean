module

public import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ClassicalGroups.McLaughlin

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsRootElt (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V) (φ : Dual K V) :
    Prop :=
  φ v = 0 ∧ ∀ c : K, ∃ g ∈ X, (g : V →ₗ[K] V) = 1 + c • φ.smulRight v

@[expose] def GenByRoots (X : Subgroup (LinearMap.GeneralLinearGroup K V)) : Prop :=
  X = Subgroup.closure {g : LinearMap.GeneralLinearGroup K V | ∃ (v : V) (φ : Dual K V),
    v ≠ 0 ∧ φ ≠ 0 ∧ IsRootElt X v φ ∧ (g : V →ₗ[K] V) = 1 + φ.smulRight v}

@[expose] def Irred (X : Subgroup (LinearMap.GeneralLinearGroup K V)) : Prop :=
  ∀ W : Submodule K V, (∀ g ∈ X, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) → W = ⊥ ∨ W = ⊤

private theorem smulRight_mul_smulRight (φ ψ : Dual K V) (v w : V) :
    φ.smulRight v * ψ.smulRight w = φ w • ψ.smulRight v := by
  ext z
  simp only [Module.End.mul_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul, smul_smul,
    LinearMap.smul_apply]
  module

theorem isRootElt_zero (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V) :
    IsRootElt X v 0 :=
  ⟨by simp, fun _ => ⟨1, X.one_mem, by simp⟩⟩

theorem isRootElt_add {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v : V}
    {φ ψ : Dual K V} (hφ : IsRootElt X v φ) (hψ : IsRootElt X v ψ) :
    IsRootElt X v (φ + ψ) := by
  refine ⟨by simp [hφ.1, hψ.1], fun c => ?_⟩
  obtain ⟨g, hg, hgv⟩ := hφ.2 c
  obtain ⟨h, hh, hhv⟩ := hψ.2 c
  refine ⟨g * h, X.mul_mem hg hh, ?_⟩
  have hsum : (φ + ψ).smulRight v = φ.smulRight v + ψ.smulRight v := by
    ext z
    simp [LinearMap.smulRight_apply, add_smul]
  have hz : φ.smulRight v * ψ.smulRight v = 0 := by
    rw [smulRight_mul_smulRight, hφ.1, zero_smul]
  rw [Units.val_mul, hgv, hhv, hsum, smul_add]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hz, smul_zero,
    add_zero]
  abel

theorem isRootElt_smul {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v : V}
    (a : K) {φ : Dual K V} (hφ : IsRootElt X v φ) : IsRootElt X v (a • φ) := by
  refine ⟨by simp [hφ.1], fun c => ?_⟩
  obtain ⟨g, hg, hgv⟩ := hφ.2 (c * a)
  have hs : (a • φ).smulRight v = a • φ.smulRight v := by
    ext z
    simp [LinearMap.smulRight_apply, smul_smul]
  exact ⟨g, hg, by rw [hgv, hs, smul_smul]⟩

@[expose] def centreForms (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V) :
    Submodule K (Dual K V) where
  carrier := {φ | IsRootElt X v φ}
  add_mem' := by
    intro φ ψ hφ hψ
    exact isRootElt_add hφ hψ
  zero_mem' := isRootElt_zero X v
  smul_mem' := by
    intro a φ hφ
    exact isRootElt_smul a hφ

@[expose] def axisSpace (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V) : Submodule K V :=
  (centreForms X v).dualCoannihilator

@[expose] def IsCentre (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V) : Prop :=
  v ≠ 0 ∧ ∃ φ : Dual K V, φ ≠ 0 ∧ IsRootElt X v φ

theorem mem_axisSpace_iff {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v x : V} :
    x ∈ axisSpace X v ↔ ∀ φ : Dual K V, IsRootElt X v φ → φ x = 0 := by
  unfold axisSpace
  rw [Submodule.mem_dualCoannihilator]
  exact Iff.rfl

private theorem units_inv_apply_apply (g : LinearMap.GeneralLinearGroup K V) (y : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) y) = y := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem isRootElt_conj {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v : V} {φ : Dual K V}
    (hx : IsRootElt X v φ) {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ X) :
    IsRootElt X ((g : V →ₗ[K] V) v)
      (φ.comp ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) := by
  refine ⟨?_, fun c => ?_⟩
  · simp [units_inv_apply_apply, hx.1]
  · obtain ⟨h, hh, hhv⟩ := hx.2 c
    refine ⟨g * h * g⁻¹, X.mul_mem (X.mul_mem hg hh) (X.inv_mem hg), ?_⟩
    have hA : (g : V →ₗ[K] V) * φ.smulRight v *
        ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
        (φ.comp ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)).smulRight
          ((g : V →ₗ[K] V) v) := by
      ext z
      simp [LinearMap.smulRight_apply]
    rw [Units.val_mul, Units.val_mul, hhv, ← hA]
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, Units.mul_inv]

private theorem commutator_rankOne {μ ν : Dual K V} {a b : V} (hμa : μ a = 0) (hνa : ν a = 0)
    (hνb : ν b = 0) (s t : K) :
    (1 + s • μ.smulRight a) * (1 + t • ν.smulRight b) * (1 + (-s) • μ.smulRight a) *
      (1 + (-t) • ν.smulRight b) = 1 + (s * t * μ b) • ν.smulRight a := by
  ext z
  simp [LinearMap.smulRight_apply, hμa, hνa, hνb]
  module

theorem isRootElt_comm {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {a b : V}
    {μ ν : Dual K V} (hx : IsRootElt X a μ) (hy : IsRootElt X b ν) (hνa : ν a = 0)
    (hμb : μ b ≠ 0) : IsRootElt X a ν := by
  refine ⟨hνa, fun c => ?_⟩
  obtain ⟨p, hp, hpv⟩ := hx.2 1
  obtain ⟨q, hq, hqv⟩ := hy.2 (c / μ b)
  obtain ⟨p', hp', hpv'⟩ := hx.2 (-1)
  obtain ⟨q', hq', hqv'⟩ := hy.2 (-(c / μ b))
  refine ⟨p * q * p' * q', X.mul_mem (X.mul_mem (X.mul_mem hp hq) hp') hq', ?_⟩
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hpv, hqv, hpv', hqv',
    commutator_rankOne hx.1 hνa hy.1, one_mul, div_mul_cancel₀ c hμb]

private theorem exists_unipotent {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v w : V}
    {φ : Dual K V} (hx : IsRootElt X v φ) (hφw : φ w ≠ 0) :
    ∃ U : K → LinearMap.GeneralLinearGroup K V, (∀ x, U x ∈ X) ∧
      ∀ x : K, (U x : V →ₗ[K] V) v = v ∧ (U x : V →ₗ[K] V) w = w + x • v ∧
        ∀ d, φ d = 0 → (U x : V →ₗ[K] V) d = d := by
  choose U hU hUe using fun x : K => hx.2 (x / φ w)
  refine ⟨U, hU, fun x => ⟨?_, ?_, fun d hd => ?_⟩⟩
  · rw [hUe x]
    simp [hx.1]
  · rw [hUe x]
    simp [LinearMap.smulRight_apply, smul_smul, div_mul_cancel₀ x hφw]
  · rw [hUe x]
    simp [LinearMap.smulRight_apply, hd]

private theorem torus_apply (U L : K → LinearMap.GeneralLinearGroup K V) {v w : V} {t : K}
    (ht : t ≠ 0) (hUv : ∀ x : K, (U x : V →ₗ[K] V) v = v)
    (hUw : ∀ x : K, (U x : V →ₗ[K] V) w = w + x • v)
    (hLv : ∀ x : K, (L x : V →ₗ[K] V) v = v + x • w)
    (hLw : ∀ x : K, (L x : V →ₗ[K] V) w = w) :
    ((U t * L (-t⁻¹) * U t * U (-1) * L 1 * U (-1) : LinearMap.GeneralLinearGroup K V) :
        V →ₗ[K] V) v = t • v ∧
      ((U t * L (-t⁻¹) * U t * U (-1) * L 1 * U (-1) : LinearMap.GeneralLinearGroup K V) :
        V →ₗ[K] V) w = t⁻¹ • w := by
  constructor
  · simp [Units.val_mul, Module.End.mul_apply, hUv, hUw, hLv, hLw, ht, mul_inv_cancel₀ ht]
  · simp [Units.val_mul, Module.End.mul_apply, hUv, hUw, hLv, hLw, ht, mul_inv_cancel₀ ht,
      inv_mul_cancel₀ ht]

theorem opposite_sl2 {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {v w : V} {φ ψ : Dual K V}
    (hx : IsRootElt X v φ) (hy : IsRootElt X w ψ) (hφw : φ w ≠ 0) (hψv : ψ v ≠ 0) :
    (∀ r ∈ Submodule.span K {v, w}, r ≠ 0 → ∃ g ∈ X, (g : V →ₗ[K] V) v = r ∧
        ∀ d, φ d = 0 → ψ d = 0 → (g : V →ₗ[K] V) d = d) ∧
      ∀ t : K, t ≠ 0 → ∃ g ∈ X, (g : V →ₗ[K] V) v = t • v ∧ (g : V →ₗ[K] V) w = t⁻¹ • w ∧
        ∀ d, φ d = 0 → ψ d = 0 → (g : V →ₗ[K] V) d = d := by
  obtain ⟨U, hUX, hU⟩ := exists_unipotent hx hφw
  obtain ⟨L, hLX, hL⟩ := exists_unipotent hy hψv
  have hUv : ∀ x : K, (U x : V →ₗ[K] V) v = v := fun x => (hU x).1
  have hUw : ∀ x : K, (U x : V →ₗ[K] V) w = w + x • v := fun x => (hU x).2.1
  have hUd : ∀ (x : K) (d : V), φ d = 0 → (U x : V →ₗ[K] V) d = d :=
    fun x d hd => (hU x).2.2 d hd
  have hLw : ∀ x : K, (L x : V →ₗ[K] V) w = w := fun x => (hL x).1
  have hLv : ∀ x : K, (L x : V →ₗ[K] V) v = v + x • w := fun x => (hL x).2.1
  have hLd : ∀ (x : K) (d : V), ψ d = 0 → (L x : V →ₗ[K] V) d = d :=
    fun x d hd => (hL x).2.2 d hd
  have hTX : ∀ t : K, U t * L (-t⁻¹) * U t * U (-1) * L 1 * U (-1) ∈ X := fun t =>
    X.mul_mem (X.mul_mem (X.mul_mem (X.mul_mem (X.mul_mem (hUX t) (hLX _)) (hUX t)) (hUX _))
      (hLX 1)) (hUX _)
  refine ⟨?_, ?_⟩
  · rintro r hr hr0
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hr
    by_cases hβ : β = 0
    · subst hβ
      have hα : α ≠ 0 := by
        rintro rfl
        exact hr0 (by simp)
      refine ⟨U α * L (-α⁻¹) * U α * U (-1) * L 1 * U (-1), hTX α, ?_, fun d hd1 hd2 => ?_⟩
      · rw [(torus_apply U L hα hUv hUw hLv hLw).1, zero_smul, add_zero]
      · simp only [Units.val_mul, Module.End.mul_apply, hUd, hLd, hd1, hd2]
    · have hy : β * ((α - 1) / β) = α - 1 := by rw [mul_div_assoc', mul_div_cancel_left₀ _ hβ]
      refine ⟨U ((α - 1) / β) * L β, X.mul_mem (hUX _) (hLX _), ?_, fun d hd1 hd2 => ?_⟩
      · simp only [Units.val_mul, Module.End.mul_apply, hLv, hUv, hUw, map_add, map_smul,
          smul_add, smul_smul, hy]
        module
      · simp only [Units.val_mul, Module.End.mul_apply, hUd, hLd, hd1, hd2]
  · intro t ht
    refine ⟨U t * L (-t⁻¹) * U t * U (-1) * L 1 * U (-1), hTX t, (torus_apply U L ht hUv hUw hLv
      hLw).1, (torus_apply U L ht hUv hUw hLv hLw).2, fun d hd1 hd2 => ?_⟩
    simp only [Units.val_mul, Module.End.mul_apply, hUd, hLd, hd1, hd2]

theorem isCentre_smul {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ X) {v : V} (hv : IsCentre X v) :
    IsCentre X ((g : V →ₗ[K] V) v) := by
  obtain ⟨hv0, φ, hφ0, hφ⟩ := hv
  refine ⟨fun h => hv0 ?_, φ.comp ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V), ?_,
    isRootElt_conj hφ hg⟩
  · have h1 := units_inv_apply_apply g v
    rw [h, map_zero] at h1
    exact h1.symm
  · intro h0
    apply hφ0
    ext y
    have h1 := LinearMap.congr_fun h0 ((g : V →ₗ[K] V) y)
    simpa [units_inv_apply_apply] using h1

section Irreducible

theorem span_isCentre_eq_top {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hirr : Irred X) (hne : ∃ v : V, IsCentre X v) :
    Submodule.span K {v : V | IsCentre X v} = ⊤ := by
  obtain ⟨v0, hv0⟩ := hne
  have hinv : ∀ g ∈ X, ∀ w ∈ Submodule.span K {v : V | IsCentre X v},
      (g : V →ₗ[K] V) w ∈ Submodule.span K {v : V | IsCentre X v} := by
    intro g hg w hw
    have hle : Submodule.span K {v : V | IsCentre X v} ≤
        (Submodule.span K {v : V | IsCentre X v}).comap (g : V →ₗ[K] V) := by
      rw [Submodule.span_le]
      intro u hu
      exact Submodule.mem_comap.mpr (Submodule.subset_span (isCentre_smul hg hu))
    exact hle hw
  rcases hirr _ hinv with h | h
  · exfalso
    have hmem : v0 ∈ Submodule.span K {v : V | IsCentre X v} := Submodule.subset_span hv0
    rw [h, Submodule.mem_bot] at hmem
    exact hv0.1 hmem
  · exact h

theorem iInf_axisSpace_eq_bot {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hirr : Irred X) (hne : ∃ v : V, IsCentre X v) :
    (⨅ v ∈ {v : V | IsCentre X v}, axisSpace X v) = ⊥ := by
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨φ, hφ0, hφ⟩ := hv0.2
  have hinv : ∀ g ∈ X, ∀ w ∈ (⨅ v ∈ {v : V | IsCentre X v}, axisSpace X v),
      (g : V →ₗ[K] V) w ∈ (⨅ v ∈ {v : V | IsCentre X v}, axisSpace X v) := by
    intro g hg w hw
    simp only [Submodule.mem_iInf, Set.mem_setOf_eq] at hw ⊢
    intro u hu
    rw [mem_axisSpace_iff]
    intro φ' hφ'
    have h1 := hw _ (isCentre_smul (X.inv_mem hg) hu)
    have h2 := mem_axisSpace_iff.mp h1 _ (isRootElt_conj hφ' (X.inv_mem hg))
    simpa using h2
  rcases hirr _ hinv with h | h
  · exact h
  · exfalso
    apply hφ0
    ext y
    have hy : y ∈ (⨅ v ∈ {v : V | IsCentre X v}, axisSpace X v) := by
      rw [h]
      exact Submodule.mem_top
    simp only [Submodule.mem_iInf, Set.mem_setOf_eq] at hy
    exact (mem_axisSpace_iff.mp (hy v0 hv0)) φ hφ

end Irreducible

end CFSG.ClassicalGroups.McLaughlin
