module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.Field.ZMod
public import CFSG.GF2Type.Smith1979.GammaU.Model

public section

namespace CFSG.GF2Type.Smith1979.GammaU

theorem theta0_theta0_theta0 (x : V12) : theta0 (theta0 (theta0 x)) = x := by
  refine ext_lo_hi (fun i => ?_) (fun i => ?_) <;>
  simp only [theta0_lo, theta0_hi] <;>
  generalize x (lo i) = a <;> generalize x (hi i) = b <;> revert a b <;> decide

@[expose] def f0 (x y : V12) : ZMod 2 := ∑ i : Fin 6, (x (lo i) * y (hi i) + x (hi i) * y (lo i))

theorem polar_q0 (x y : V12) : QuadraticMap.polar q0 x y = f0 x y := by
  simp only [QuadraticMap.polar, q0, f0, Pi.add_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem lo_ne_hi (i j : Fin 6) : lo i ≠ hi j := by
  intro h
  have h' := congrArg Fin.val h
  simp only [lo, hi, Fin.coe_castAdd, Fin.coe_natAdd] at h'
  omega

theorem hi_inj {i j : Fin 6} (h : hi i = hi j) : i = j := by
  have h' := congrArg Fin.val h
  simp only [hi, Fin.coe_natAdd] at h'
  exact Fin.ext (by omega)

theorem lo_inj {i j : Fin 6} (h : lo i = lo j) : i = j := by
  have h' := congrArg Fin.val h
  simp only [lo, Fin.coe_castAdd] at h'
  exact Fin.ext h'

theorem f0_unit_hi (x : V12) (i : Fin 6) : f0 x (Pi.single (hi i) 1) = x (lo i) := by
  simp only [f0]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne (lo_ne_hi i i), mul_one, mul_zero, add_zero]
  · intro j _ hji
    rw [Pi.single_eq_of_ne (fun h => hji (hi_inj h)), Pi.single_eq_of_ne (lo_ne_hi j i),
      mul_zero, mul_zero, add_zero]
  · simp

theorem f0_unit_lo (x : V12) (i : Fin 6) : f0 x (Pi.single (lo i) 1) = x (hi i) := by
  simp only [f0]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne (fun h => lo_ne_hi i i h.symm), mul_one,
      mul_zero, zero_add]
  · intro j _ hji
    rw [Pi.single_eq_of_ne (fun h => hji (lo_inj h)),
      Pi.single_eq_of_ne (fun h => lo_ne_hi i j h.symm), mul_zero, mul_zero, add_zero]
  · simp

theorem eq_zero_of_f0 {x : V12} (h : ∀ y, f0 x y = 0) : x = 0 :=
  ext_lo_hi (fun i => by rw [← f0_unit_hi x i, h]; rfl)
    (fun i => by rw [← f0_unit_lo x i, h]; rfl)

theorem injective_of_preserves_q0 {g : V12 →ₗ[ZMod 2] V12} (hg : ∀ x, q0 (g x) = q0 x) :
    Function.Injective g := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine eq_zero_of_f0 fun y => ?_
  rw [← polar_q0, ← (show QuadraticMap.polar q0 (g x) (g y) = QuadraticMap.polar q0 x y by
    simp only [QuadraticMap.polar, ← map_add, hg]), hx, polar_q0]
  simp [f0]

@[expose] noncomputable def equivOfPreserves (g : V12 →ₗ[ZMod 2] V12)
    (hg : ∀ x, q0 (g x) = q0 x) : V12 ≃ₗ[ZMod 2] V12 :=
  LinearEquiv.ofInjectiveEndo g (injective_of_preserves_q0 hg)

@[simp] theorem equivOfPreserves_apply (g : V12 →ₗ[ZMod 2] V12) (hg : ∀ x, q0 (g x) = q0 x)
    (x : V12) : equivOfPreserves g hg x = g x := rfl

theorem apply_inv_apply (g : V12 ≃ₗ[ZMod 2] V12) (y : V12) : g (g⁻¹ y) = y :=
  g.apply_symm_apply y

@[expose] def NormTheta (g : V12 → V12) : Prop :=
  (∀ x, g (theta0 x) = theta0 (g x)) ∨ ∀ x, g (theta0 x) = theta0 (theta0 (g x))

@[expose] def gammaU : Subgroup (V12 ≃ₗ[ZMod 2] V12) where
  carrier := {g | (∀ x, q0 (g x) = q0 x) ∧ NormTheta g}
  one_mem' := ⟨fun _ => rfl, Or.inl fun _ => rfl⟩
  mul_mem' {g h} hg hh := by
    refine ⟨fun x => by simp only [LinearEquiv.mul_apply, hg.1, hh.1], ?_⟩
    simp only [NormTheta, LinearEquiv.mul_apply]
    rcases hg.2 with hg2 | hg2 <;> rcases hh.2 with hh2 | hh2
    · exact Or.inl fun x => by rw [hh2, hg2]
    · exact Or.inr fun x => by rw [hh2, hg2, hg2]
    · exact Or.inr fun x => by rw [hh2, hg2]
    · exact Or.inl fun x => by rw [hh2, hg2, hg2, theta0_theta0_theta0]
  inv_mem' {g} hg := by
    refine ⟨fun x => by
      have h := hg.1 (g⁻¹ x)
      rw [apply_inv_apply] at h
      exact h.symm, ?_⟩
    rcases hg.2 with hg2 | hg2
    · refine Or.inl fun x => g.injective ?_
      change g (g⁻¹ (theta0 x)) = g (theta0 (g⁻¹ x))
      rw [hg2, apply_inv_apply, apply_inv_apply]
    · refine Or.inr fun x => g.injective ?_
      change g (g⁻¹ (theta0 x)) = g (theta0 (theta0 (g⁻¹ x)))
      rw [hg2, hg2, apply_inv_apply, apply_inv_apply, theta0_theta0_theta0]

theorem mem_gammaU {g : V12 ≃ₗ[ZMod 2] V12} :
    g ∈ gammaU ↔ (∀ x, q0 (g x) = q0 x) ∧ NormTheta g := Iff.rfl

end CFSG.GF2Type.Smith1979.GammaU
