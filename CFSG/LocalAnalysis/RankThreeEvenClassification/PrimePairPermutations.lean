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

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem prime_power_permutation_preserving_pair_fixes {points : Type u}
    (prime : ℕ) (hodd : Odd prime) (permutation : Equiv.Perm points)
    (exponent : ℕ) (hpower : permutation ^ (prime ^ exponent) = 1)
    (first second : points) (hne : first ≠ second)
    (hpreserves : ∀ point : points, permutation point ∈ ({first, second} : Set points) ↔
      point ∈ ({first, second} : Set points)) :
    permutation first = first ∧ permutation second = second := by
  classical
  let pair := ({first, second} : Set points)
  let restricted := permutation.subtypePerm hpreserves
  have hiterate : ∀ power : ℕ, ∀ point : pair, ((restricted ^ power) point : points) =
      (permutation ^ power) (point : points) := by
    intro power
    induction power with
    | zero => intro point; rfl
    | succ power ih =>
      intro point
      rw [pow_succ', pow_succ']
      change permutation (((restricted ^ power) point : pair) : points) =
        permutation ((permutation ^ power) (point : points))
      rw [ih]
  have hrestrictedPower : restricted ^ (prime ^ exponent) = 1 := by
    apply Equiv.ext
    intro point
    apply Subtype.ext
    rw [hiterate, hpower]
    rfl
  have hcard : Nat.card (Equiv.Perm pair) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hpairCard : Fintype.card pair = 2 := by
      rw [← Nat.card_eq_fintype_card]
      change ({first, second} : Set points).ncard = 2
      exact Set.ncard_pair hne
    rw [hpairCard]
    decide
  have horderTwo : orderOf restricted ∣ 2 := hcard ▸ orderOf_dvd_natCard restricted
  have horderPrime : orderOf restricted ∣ prime ^ exponent :=
    orderOf_dvd_iff_pow_eq_one.mpr hrestrictedPower
  have horderOne : orderOf restricted = 1 := by
    have hcoprime : Nat.Coprime 2 (prime ^ exponent) := hodd.coprime_two_left.pow_right exponent
    have hdivisor := Nat.dvd_gcd horderTwo horderPrime
    rw [hcoprime.gcd_eq_one] at hdivisor
    exact Nat.eq_one_of_dvd_one hdivisor
  have heq : restricted = 1 := orderOf_eq_one_iff.mp horderOne
  constructor
  · exact congrArg (fun value : pair => (value : points))
      (DFunLike.congr_fun heq (⟨first, Set.mem_insert _ _⟩ : pair))
  · exact congrArg (fun value : pair => (value : points))
      (DFunLike.congr_fun heq (⟨second, Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩ : pair))

end CFSG.RankThreeEvenClassification.Helpers
