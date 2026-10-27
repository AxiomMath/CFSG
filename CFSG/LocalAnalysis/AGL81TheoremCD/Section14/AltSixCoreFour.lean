module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem apply_apply_eq_self {f : V ≃ₗ[K] V} (hf : f ^ 2 = 1) (x : V) :
    f (f x) = x := by
  have h := congrArg (fun e : V ≃ₗ[K] V => e x) hf
  simpa [pow_two, LinearEquiv.mul_apply] using h

private theorem exists_ne_zero_apply_eq_neg {v : V ≃ₗ[K] V} (hv : v ^ 2 = 1) (hv1 : v ≠ 1) :
    ∃ z : V, z ≠ 0 ∧ v z = -z := by
  classical
  have h : ∃ y : V, v y ≠ y := by
    by_contra h
    push Not at h
    exact hv1 (LinearEquiv.ext fun x => by simpa using h x)
  obtain ⟨y, hy⟩ := h
  refine ⟨y - v y, ?_, ?_⟩
  · intro hz
    exact hy (sub_eq_zero.mp hz).symm
  · rw [map_sub, apply_apply_eq_self hv y]
    abel

private theorem mul_conj_eqs {u v w : V ≃ₗ[K] V} (hw : w ^ 3 = 1)
    (hwu : w * u * w⁻¹ = v) (hwv : w * v * w⁻¹ = u * v) :
    v * w = w * u ∧ u * w = w * u * v ∧ u * w ^ 2 = w ^ 2 * v := by
  have h32 : w ^ 2 * w = 1 := by simpa [pow_succ] using hw
  have hww : w ^ 2 = w⁻¹ := eq_inv_of_mul_eq_one_left h32
  have hwinv : (w ^ 2)⁻¹ = w := inv_eq_of_mul_eq_one_right h32
  have h1 : v * w = w * u := by
    calc v * w = (w * u * w⁻¹) * w := by rw [hwu]
      _ = w * u := by group
  have h2 : u * w = w * u * v := by
    have hconj : w ^ 2 * u * (w ^ 2)⁻¹ = u * v := by
      calc w ^ 2 * u * (w ^ 2)⁻¹ = w * (w * u * w⁻¹) * w⁻¹ := by
            rw [← inv_pow, pow_two, pow_two]
            group
        _ = w * v * w⁻¹ := by rw [hwu]
        _ = u * v := hwv
    calc u * w = u * (w ^ 2)⁻¹ := by rw [hwinv]
      _ = (w ^ 2)⁻¹ * (w ^ 2 * u * (w ^ 2)⁻¹) := by group
      _ = (w ^ 2)⁻¹ * (u * v) := by rw [hconj]
      _ = w * (u * v) := by rw [hwinv]
      _ = w * u * v := by group
  have h3 : u * w ^ 2 = w ^ 2 * v := by
    calc u * w ^ 2 = u * w⁻¹ := by rw [hww]
      _ = (w ^ 2 * w) * u * w⁻¹ := by rw [h32, one_mul]
      _ = w ^ 2 * (w * u * w⁻¹) := by group
      _ = w ^ 2 * v := by rw [hwu]
  exact ⟨h1, h2, h3⟩

private theorem apply_mul_conj_eqs {u v w : V ≃ₗ[K] V}
    (h : v * w = w * u ∧ u * w = w * u * v ∧ u * w ^ 2 = w ^ 2 * v) :
    (∀ x, v (w x) = w (u x)) ∧ (∀ x, u (w x) = w (u (v x))) ∧
      (∀ x, u (w (w x)) = w (w (v x))) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have := congrArg (fun e : V ≃ₗ[K] V => e x) h1
    simpa [LinearEquiv.mul_apply] using this
  · intro x
    have := congrArg (fun e : V ≃ₗ[K] V => e x) h2
    simpa [LinearEquiv.mul_apply] using this
  · intro x
    have := congrArg (fun e : V ≃ₗ[K] V => e x) h3
    simpa [pow_two, LinearEquiv.mul_apply] using this

private theorem exists_fixed_neg_of_klein {u v w : V ≃ₗ[K] V} (hu : u ^ 2 = 1)
    (hv : v ^ 2 = 1) (huv : Commute u v) (hvw : ∀ x, v (w x) = w (u x))
    (huw : ∀ x, u (w x) = w (u (v x))) (hu1 : u ≠ 1) :
    ∃ x₀ : V, x₀ ≠ 0 ∧ u x₀ = x₀ ∧ v x₀ = -x₀ := by
  have huu : ∀ x, u (u x) = x := fun x => apply_apply_eq_self hu x
  have huv' : ∀ x, u (v x) = v (u x) := by
    intro x
    have h := congrArg (fun e : V ≃ₗ[K] V => e x) huv.eq
    simpa [LinearEquiv.mul_apply] using h
  have hv1 : v ≠ 1 := by
    intro h
    apply hu1
    ext x
    have hx : w x = w (u x) := by simpa [h] using hvw x
    exact (w.injective hx).symm
  obtain ⟨z, hz0, hvz⟩ := exists_ne_zero_apply_eq_neg hv hv1
  by_cases hsum : z + u z = 0
  · have huz : u z = -z := eq_neg_of_add_eq_zero_right hsum
    refine ⟨w z, ?_, ?_, ?_⟩
    · exact (LinearEquiv.map_ne_zero_iff w).mpr hz0
    · calc u (w z) = w (u (v z)) := huw z
        _ = w (u (-z)) := by rw [hvz]
        _ = w (-(u z)) := by rw [map_neg]
        _ = w (-(-z)) := by rw [huz]
        _ = w z := by rw [neg_neg]
    · calc v (w z) = w (u z) := hvw z
        _ = w (-z) := by rw [huz]
        _ = - w z := by rw [map_neg]
  · refine ⟨z + u z, hsum, ?_, ?_⟩
    · rw [map_add, huu]
      abel
    · rw [map_add, hvz, ← huv' z, hvz, map_neg]
      abel

private theorem step_two (h2 : (2 : K) ≠ 0) {u v w : V ≃ₗ[K] V} (hw : w ^ 3 = 1)
    (huw : ∀ x, u (w x) = w (u (v x)))
    (huw2 : ∀ x, u (w (w x)) = w (w (v x))) {x₀ : V} (hx0 : x₀ ≠ 0)
    (hux0 : u x₀ = x₀) (hvx0 : v x₀ = -x₀) : ∃ x : V, x ≠ 0 ∧ w x = x := by
  let x : V := x₀ + w x₀ + w (w x₀)
  have hux : u x = x₀ - w x₀ - w (w x₀) := by
    dsimp [x]
    rw [map_add, map_add, hux0]
    have h1 : u (w x₀) = - w x₀ := by
      calc u (w x₀) = w (u (v x₀)) := huw x₀
        _ = w (u (-x₀)) := by rw [hvx0]
        _ = w (-(u x₀)) := by rw [map_neg]
        _ = w (-x₀) := by rw [hux0]
        _ = - w x₀ := by rw [map_neg]
    have h2' : u (w (w x₀)) = - w (w x₀) := by
      calc u (w (w x₀)) = w (w (v x₀)) := huw2 x₀
        _ = w (w (-x₀)) := by rw [hvx0]
        _ = w (-(w x₀)) := by rw [map_neg]
        _ = - w (w x₀) := by rw [map_neg]
    rw [h1, h2']
    abel
  have hwxxx : w (w (w x₀)) = x₀ := by
    have h := congrArg (fun e : V ≃ₗ[K] V => e x₀) hw
    simpa [pow_succ, pow_two, LinearEquiv.mul_apply] using h
  have hwx : w x = x := by
    dsimp [x]
    rw [map_add, map_add, hwxxx]
    abel
  refine ⟨x, ?_, hwx⟩
  intro hx
  have hsum : x + u x = (2 : K) • x₀ := by
    rw [hux]
    dsimp [x]
    rw [two_smul]
    abel
  rw [hx] at hsum
  have hzero : (2 : K) • x₀ = 0 := by simpa using hsum.symm
  exact (smul_ne_zero h2 hx0) hzero

theorem exists_ne_zero_apply_eq_of_klein {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (h2 : (2 : K) ≠ 0) {u v w : V ≃ₗ[K] V} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (huv : Commute u v) (hw : w ^ 3 = 1) (hwu : w * u * w⁻¹ = v) (hwv : w * v * w⁻¹ = u * v)
    (hu1 : u ≠ 1) : ∃ x : V, x ≠ 0 ∧ w x = x := by
  obtain ⟨h1, h2', h3⟩ := mul_conj_eqs hw hwu hwv
  obtain ⟨hvw, huw, huw2⟩ := apply_mul_conj_eqs ⟨h1, h2', h3⟩
  obtain ⟨x₀, hx0, hux0, hvx0⟩ := exists_fixed_neg_of_klein hu hv huv hvw huw hu1
  exact step_two h2 hw huw huw2 hx0 hux0 hvx0

theorem one_le_finrank_ker_of_klein {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {u v w : V ≃ₗ[K] V} (hu : u ^ 2 = 1)
    (hv : v ^ 2 = 1) (huv : Commute u v) (hw : w ^ 3 = 1) (hwu : w * u * w⁻¹ = v)
    (hwv : w * v * w⁻¹ = u * v) (hu1 : u ≠ 1) :
    1 ≤ Module.finrank K ↥(LinearMap.ker (w.toLinearMap - 1)) := by
  obtain ⟨x, hx0, hwx⟩ := exists_ne_zero_apply_eq_of_klein h2 hu hv huv hw hwu hwv hu1
  have hxker : x ∈ LinearMap.ker (w.toLinearMap - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    simp [hwx]
  have hxsub : (⟨x, hxker⟩ : ↥(LinearMap.ker (w.toLinearMap - 1))) ≠ 0 := by
    intro h
    exact hx0 (by simpa using congrArg Subtype.val h)
  have hpos : 0 < Module.finrank K ↥(LinearMap.ker (w.toLinearMap - 1)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨x, hxker⟩, hxsub⟩
  exact hpos

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core
