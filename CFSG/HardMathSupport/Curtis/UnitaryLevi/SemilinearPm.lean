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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

section FieldFour

variable {K : Type*} [Field K]

theorem units_pow_three_eq_one_of_card_four (hK : Nat.card K = 4) (x : Kˣ) : x ^ 3 = 1 := by
  have h : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← h]
  exact pow_card_eq_one'

theorem pow_three_eq_one_of_card_four (hK : Nat.card K = 4) {y : K} (hy : y ≠ 0) :
    y ^ 3 = 1 := by
  have := units_pow_three_eq_one_of_card_four hK (Units.mk0 y hy)
  simpa using congrArg Units.val this

theorem sq_add_self_add_one_eq_zero_of_card_four (hK : Nat.card K = 4) {y : K} (hy0 : y ≠ 0)
    (hy1 : y ≠ 1) : y ^ 2 + y + 1 = 0 := by
  have h3 := pow_three_eq_one_of_card_four hK hy0
  have : (y - 1) * (y ^ 2 + y + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hy1
  · exact h

theorem eq_or_eq_sq_of_roots {ω y : K} (hω : ω ^ 2 + ω + 1 = 0) (hy : y ^ 2 + y + 1 = 0) :
    y = ω ∨ y = ω ^ 2 := by
  have : (y - ω) * (y - ω ^ 2) = 0 := by linear_combination hy + (ω - 1 - y) * hω
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

theorem ringEquiv_apply_eq_sq_of_card_four (hK : Nat.card K = 4) {φ : K ≃+* K} (hφ : φ ≠ 1)
    (x : K) : φ x = x ^ 2 := by
  by_contra hx
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero]; ring)
  have hx1 : x ≠ 1 := fun h => hx (by rw [h, map_one]; ring)
  have hroot : ∀ y : K, y ≠ 0 → y ≠ 1 → φ y = y ∨ φ y = y ^ 2 := by
    intro y hy0 hy1
    have hy := sq_add_self_add_one_eq_zero_of_card_four hK hy0 hy1
    have hφy : (φ y) ^ 2 + φ y + 1 = 0 := by
      have := congrArg φ hy
      simpa using this
    exact eq_or_eq_sq_of_roots (ω := y) hy hφy
  have hfix : φ x = x := (hroot x hx0 hx1).resolve_right hx
  have hωx := sq_add_self_add_one_eq_zero_of_card_four hK hx0 hx1
  apply hφ
  ext y
  by_cases hy0 : y = 0
  · simp [hy0]
  by_cases hy1 : y = 1
  · simp [hy1]
  have hy := sq_add_self_add_one_eq_zero_of_card_four hK hy0 hy1
  rcases eq_or_eq_sq_of_roots hωx hy with h | h
  · rw [h, hfix]; rfl
  · rw [h, map_pow, hfix]; rfl

end FieldFour

section Transport

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_eigenspace_eq (φ : K ≃+* K) (τ : V ≃+ V) (hτ : ∀ c v, τ (c • v) = φ c • τ v)
    (f f' : V →ₗ[K] V) (hff' : ∀ v, f' (τ v) = τ (f v)) (a : K) :
    Module.finrank K (Module.End.eigenspace f a) =
      Module.finrank K (Module.End.eigenspace f' (φ a)) := by
  let j : Module.End.eigenspace f a ≃+ Module.End.eigenspace f' (φ a) :=
    { toFun := fun v => ⟨τ v, by
        rw [Module.End.mem_eigenspace_iff, hff', (Module.End.mem_eigenspace_iff.mp v.2), hτ]⟩
      invFun := fun w => ⟨τ.symm w, by
        rw [Module.End.mem_eigenspace_iff]
        apply τ.injective
        rw [← hff', AddEquiv.apply_symm_apply, (Module.End.mem_eigenspace_iff.mp w.2), hτ,
          AddEquiv.apply_symm_apply]⟩
      left_inv := fun v => by ext; simp
      right_inv := fun w => by ext; simp
      map_add' := fun v w => by ext; simp }
  have h := rank_eq_of_equiv_equiv (R := K) (R' := K) (φ : K → K) j φ.bijective
    (fun r m => by ext; exact hτ r m)
  simp only [Module.finrank, h]

end Transport

end CFSG.HardMathSupport.Curtis.UnitaryLevi
