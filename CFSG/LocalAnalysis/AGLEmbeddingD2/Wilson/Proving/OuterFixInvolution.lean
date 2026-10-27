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

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem exists_outer_involution_of_fix_eq {J : Type*} [Group J] {y : J} (hy3 : y ^ 3 = 1)
    (τ : MulAut J) (hτo : τ ∉ (MulAut.conj : J →* MulAut J).range) (hτy : τ y = y) {i : ℕ}
    (hτ2 : τ ^ 2 = MulAut.conj (y ^ i)) :
    (τ * MulAut.conj (y ^ i)) ^ 2 = 1 ∧
      τ * MulAut.conj (y ^ i) ∉ (MulAut.conj : J →* MulAut J).range ∧
      (τ * MulAut.conj (y ^ i)) y = y := by
  have hτyi : τ (y ^ i) = y ^ i := by
    rw [map_pow, hτy]
  have hcomm : Commute τ (MulAut.conj (y ^ i)) := by
    show τ * MulAut.conj (y ^ i) = MulAut.conj (y ^ i) * τ
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hτyi]
  have hyi3 : (y ^ i) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hy3, one_pow]
  have hc3 : (MulAut.conj (y ^ i)) ^ 3 = 1 := by
    rw [← map_pow, hyi3, map_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcomm.mul_pow 2, hτ2]
    rw [← pow_succ' (MulAut.conj (y ^ i)) 2]
    exact hc3
  · rintro ⟨g, hg⟩
    apply hτo
    refine ⟨g * (y ^ i)⁻¹, ?_⟩
    have hτeq : τ = MulAut.conj g * (MulAut.conj (y ^ i))⁻¹ := by
      rw [hg, mul_inv_cancel_right]
    rw [map_mul, map_inv, hτeq]
  · have hy_comm : y ^ i * y * (y ^ i)⁻¹ = y := by
      rw [(Commute.refl y).pow_left i |>.eq, mul_inv_cancel_right]
    rw [MulAut.mul_apply, MulAut.conj_apply, hy_comm, hτy]

end CFSG.AGLEmbeddingD2.Wilson.Proving
