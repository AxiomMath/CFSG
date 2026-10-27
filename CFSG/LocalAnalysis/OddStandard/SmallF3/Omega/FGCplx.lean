module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

structure FGCplx (B : LinearMap.BilinForm (ZMod 3) V) (ρ : V →ₗ[ZMod 3] V) (lam : ZMod 3) :
    Prop where
  symm : ∀ x y, B x y = B y x
  lam_eq : lam = 1 ∨ lam = -1
  sq : ∀ v, ρ (ρ v) = -v
  isom : ∀ x y, B (ρ x) (ρ y) = lam * B x y

structure FGCplxGroup (B : LinearMap.BilinForm (ZMod 3) V) (ρ : V →ₗ[ZMod 3] V)
    (H : Subgroup (V ≃ₗ[ZMod 3] V)) : Prop where
  isom : ∀ g ∈ H, ∀ x y, B (g x) (g y) = B x y
  comm : ∀ g ∈ H, ∀ x, g (ρ x) = ρ (g x)
  normal : ∀ σ : V ≃ₗ[ZMod 3] V, (∀ x y, B (σ x) (σ y) = B x y) → (∀ x, σ (ρ x) = ρ (σ x)) →
    ∀ g ∈ H, σ * g * σ⁻¹ ∈ H

variable {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V} {lam : ZMod 3}

theorem FGCplx.adj (h : FGCplx B ρ lam) (x y : V) : B (ρ x) y = -lam * B x (ρ y) := by
  have h1 := h.isom x (ρ y)
  rw [h.sq y, map_neg] at h1
  linear_combination -h1

theorem FGCplx.pair_zero (h : FGCplx B ρ lam) (hl : lam = 1) (v : V) : B v (ρ v) = 0 := by
  have h1 := h.adj v v
  rw [h.symm (ρ v) v, hl] at h1
  have h2 : (2 : ZMod 3) * B v (ρ v) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

end CFSG.OddStandard.SmallF3.Omega
