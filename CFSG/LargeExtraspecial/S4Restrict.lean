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

namespace CFSG.LargeExtraspecial.S4

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def restrictEquiv (e : V ≃ₗ[K] V) (U : Submodule K V) (h₁ : ∀ u ∈ U, e u ∈ U)
    (h₂ : ∀ u ∈ U, e.symm u ∈ U) : U ≃ₗ[K] U where
  toFun u := ⟨e (u : V), h₁ u u.2⟩
  invFun u := ⟨e.symm (u : V), h₂ u u.2⟩
  map_add' u w := Subtype.ext (map_add e (u : V) (w : V))
  map_smul' c u := Subtype.ext (map_smul e c (u : V))
  left_inv u := Subtype.ext (e.symm_apply_apply (u : V))
  right_inv u := Subtype.ext (e.apply_symm_apply (u : V))

@[simp] theorem coe_restrictEquiv_apply (e : V ≃ₗ[K] V) (U : Submodule K V)
    (h₁ : ∀ u ∈ U, e u ∈ U) (h₂ : ∀ u ∈ U, e.symm u ∈ U) (u : U) :
    ((restrictEquiv e U h₁ h₂ u : U) : V) = e (u : V) :=
  rfl

@[expose] noncomputable def restrictHom {H : Type*} [Group H] (φ : H →* (V ≃ₗ[K] V))
    (U : Submodule K V) (hU : ∀ x u, u ∈ U → φ x u ∈ U) : H →* (U ≃ₗ[K] U) where
  toFun x := restrictEquiv (φ x) U (fun u hu => hU x u hu) (fun u hu => by
    have : (φ x).symm = φ x⁻¹ := by rw [map_inv]; rfl
    rw [this]
    exact hU x⁻¹ u hu)
  map_one' := LinearEquiv.ext fun u => Subtype.ext (by simp)
  map_mul' x y := LinearEquiv.ext fun u => Subtype.ext (by simp [map_mul])

@[simp] theorem coe_restrictHom_apply {H : Type*} [Group H] (φ : H →* (V ≃ₗ[K] V))
    (U : Submodule K V) (hU : ∀ x u, u ∈ U → φ x u ∈ U) (x : H) (u : U) :
    ((restrictHom φ U hU x u : U) : V) = φ x (u : V) :=
  rfl

theorem restrictHom_eq_one_iff {H : Type*} [Group H] (φ : H →* (V ≃ₗ[K] V))
    (U : Submodule K V) (hU : ∀ x u, u ∈ U → φ x u ∈ U) (x : H) :
    restrictHom φ U hU x = 1 ↔ ∀ u ∈ U, φ x u = u := by
  constructor
  · intro h u hu
    have := congrArg (fun e : U ≃ₗ[K] U => ((e ⟨u, hu⟩ : U) : V)) h
    simpa using this
  · intro h
    exact LinearEquiv.ext fun u => Subtype.ext (by simpa using h u u.2)

theorem restrictHom_apply_sub {H : Type*} [Group H] (φ : H →* (V ≃ₗ[K] V))
    (U : Submodule K V) (hU : ∀ x u, u ∈ U → φ x u ∈ U) (x : H) (u : U) :
    ((restrictHom φ U hU x u - u : U) : V) = φ x (u : V) - (u : V) :=
  rfl

end CFSG.LargeExtraspecial.S4
