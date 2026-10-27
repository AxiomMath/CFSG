module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LargeExtraspecial.AS35YF

open Equiv Equiv.Perm

@[expose] def qm4 (x : Fin (2 * 2) → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 2 * x 2 + x 2 * x 3 + x 3 * x 3

@[expose] def bm4 (x y : Fin (2 * 2) → ZMod 2) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2

@[expose] def ext5 (x : Fin (2 * 2) → ZMod 2) : Fin 5 → ZMod 2 :=
  ![x 0 + x 1 + x 2, x 0 + x 1 + x 2 + x 3, x 0 + x 1 + x 3, x 0, x 1]

@[expose] def proj5 (y : Fin 5 → ZMod 2) : Fin (2 * 2) → ZMod 2 :=
  ![y 3, y 4, y 0 + y 3 + y 4, y 0 + y 1]

@[expose] def act5 (σ : Perm (Fin 5)) (x : Fin (2 * 2) → ZMod 2) : Fin (2 * 2) → ZMod 2 :=
  proj5 fun k => ext5 x (σ⁻¹ k)

@[expose] def vv (i j : Fin 5) : Fin (2 * 2) → ZMod 2 :=
  proj5 fun k => if k = i ∨ k = j then 1 else 0

theorem sum_ext5 : ∀ x : Fin (2 * 2) → ZMod 2, ∑ k, ext5 x k = 0 := by
  decide

theorem ext5_proj5 : ∀ y : Fin 5 → ZMod 2, ∑ k, y k = 0 → ext5 (proj5 y) = y := by
  decide

theorem proj5_ext5 : ∀ x : Fin (2 * 2) → ZMod 2, proj5 (ext5 x) = x := by
  decide

set_option maxRecDepth 100000 in
theorem act5_swap : ∀ i j : Fin 5, i ≠ j → ∀ x : Fin (2 * 2) → ZMod 2,
    act5 (swap i j) x = x + bm4 x (vv i j) • vv i j := by
  decide

set_option maxRecDepth 100000 in
theorem qm4_vv : ∀ i j : Fin 5, i ≠ j → qm4 (vv i j) = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem exists_eq_vv : ∀ x : Fin (2 * 2) → ZMod 2, qm4 x = 1 →
    ∃ i j : Fin 5, i ≠ j ∧ x = vv i j := by
  decide

set_option maxRecDepth 100000 in
theorem eq_one_of_act5 : ∀ σ : Perm (Fin 5), act5 σ ![1, 0, 0, 0] = ![1, 0, 0, 0] →
    act5 σ ![0, 1, 0, 0] = ![0, 1, 0, 0] → act5 σ ![0, 0, 1, 0] = ![0, 0, 1, 0] →
    act5 σ ![0, 0, 0, 1] = ![0, 0, 0, 1] → σ = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem qm4_act5 : ∀ σ : Perm (Fin 5), ∀ x : Fin (2 * 2) → ZMod 2,
    qm4 (act5 σ x) = qm4 x := by
  decide

theorem ext5_act5 (σ : Perm (Fin 5)) (x : Fin (2 * 2) → ZMod 2) :
    ext5 (act5 σ x) = fun k => ext5 x (σ⁻¹ k) :=
  ext5_proj5 _ (by rw [Equiv.sum_comp σ⁻¹ (ext5 x)]; exact sum_ext5 x)

theorem act5_one (x : Fin (2 * 2) → ZMod 2) : act5 1 x = x :=
  proj5_ext5 x

theorem act5_mul (σ τ : Perm (Fin 5)) (x : Fin (2 * 2) → ZMod 2) :
    act5 (σ * τ) x = act5 σ (act5 τ x) := by
  change proj5 (fun k => ext5 x ((σ * τ)⁻¹ k)) = proj5 (fun k => ext5 (act5 τ x) (σ⁻¹ k))
  rw [ext5_act5, mul_inv_rev]
  rfl

theorem ext5_add (x y : Fin (2 * 2) → ZMod 2) : ext5 (x + y) = ext5 x + ext5 y := by
  funext k
  fin_cases k <;> simp [ext5] <;> ring

theorem proj5_add (u w : Fin 5 → ZMod 2) : proj5 (u + w) = proj5 u + proj5 w := by
  funext k
  fin_cases k <;> simp [proj5] <;> ring

theorem ext5_smul (c : ZMod 2) (x : Fin (2 * 2) → ZMod 2) : ext5 (c • x) = c • ext5 x := by
  funext k
  fin_cases k <;> simp [ext5] <;> ring

theorem proj5_smul (c : ZMod 2) (u : Fin 5 → ZMod 2) : proj5 (c • u) = c • proj5 u := by
  funext k
  fin_cases k <;> simp [proj5] <;> ring

theorem act5_add (σ : Perm (Fin 5)) (x y : Fin (2 * 2) → ZMod 2) :
    act5 σ (x + y) = act5 σ x + act5 σ y := by
  rw [act5, act5, act5, ← proj5_add, ext5_add]
  rfl

theorem act5_smul (σ : Perm (Fin 5)) (c : ZMod 2) (x : Fin (2 * 2) → ZMod 2) :
    act5 σ (c • x) = c • act5 σ x := by
  rw [act5, act5, ← proj5_smul, ext5_smul]
  rfl

@[expose] def act5L (σ : Perm (Fin 5)) :
    (Fin (2 * 2) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * 2) → ZMod 2) where
  toFun := act5 σ
  invFun := act5 σ⁻¹
  map_add' := act5_add σ
  map_smul' := act5_smul σ
  left_inv x := by rw [← act5_mul, inv_mul_cancel, act5_one]
  right_inv x := by rw [← act5_mul, mul_inv_cancel, act5_one]

@[expose] def act5Hom :
    Perm (Fin 5) →* ((Fin (2 * 2) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * 2) → ZMod 2)) where
  toFun := act5L
  map_one' := LinearEquiv.ext act5_one
  map_mul' σ τ := LinearEquiv.ext (act5_mul σ τ)

end CFSG.LargeExtraspecial.AS35YF
