module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OrderReductions.NormThreeCoefficients

theorem exists_two_signed_coefficients {index : Type*} [DecidableEq index] (coefficients : index →₀ ℤ)
    (principal : index) (principal_one : coefficients principal = 1)
    (norm_three : (∑ current ∈ coefficients.support, coefficients current ^ 2) = 3) :
    ∃ first second : index, first ≠ second ∧ first ≠ principal ∧ second ≠ principal ∧
      (coefficients first = 1 ∨ coefficients first = -1) ∧
      (coefficients second = 1 ∨ coefficients second = -1) ∧
      coefficients.support = {principal, first, second} := by
  classical
  have principal_mem : principal ∈ coefficients.support := Finsupp.mem_support_iff.mpr (by omega)
  let rest := coefficients.support.erase principal
  have remaining_norm : (∑ current ∈ rest, coefficients current ^ 2) = 2 := by
    have split := Finset.sum_erase_add coefficients.support (fun current => coefficients current ^ 2)
      principal_mem
    rw [principal_one, norm_three] at split
    dsimp [rest]
    omega
  have signs : ∀ current ∈ rest, coefficients current = 1 ∨ coefficients current = -1 := by
    intro current current_mem
    have square_upper := Finset.single_le_sum
      (fun other (_ : other ∈ rest) => sq_nonneg (coefficients other)) current_mem
    rw [remaining_norm] at square_upper
    have coefficient_ne_zero : coefficients current ≠ 0 :=
      Finsupp.mem_support_iff.mp (Finset.mem_of_mem_erase current_mem)
    have lower : -1 ≤ coefficients current := by nlinarith
    have upper : coefficients current ≤ 1 := by nlinarith
    omega
  have rest_card : rest.card = 2 := by
    have squares_one : ∀ current ∈ rest, coefficients current ^ 2 = 1 := by
      intro current membership
      rcases signs current membership with equal | equal <;> rw [equal] <;> norm_num
    rw [Finset.sum_congr rfl squares_one, Finset.sum_const, nsmul_eq_mul, mul_one] at remaining_norm
    exact_mod_cast remaining_norm
  obtain ⟨first, second, distinct, rest_eq⟩ := Finset.card_eq_two.mp rest_card
  have first_mem : first ∈ rest := by rw [rest_eq]; simp
  have second_mem : second ∈ rest := by rw [rest_eq]; simp
  refine ⟨first, second, distinct, (Finset.mem_erase.mp first_mem).1,
    (Finset.mem_erase.mp second_mem).1, signs first first_mem, signs second second_mem, ?_⟩
  have insert_eq := Finset.insert_erase principal_mem
  change insert principal rest = coefficients.support at insert_eq
  rw [rest_eq] at insert_eq
  exact insert_eq.symm

theorem norm_three_expansion {index : Type*} (coefficients : index →₀ ℤ)
    (principal : index) (principal_one : coefficients principal = 1)
    (norm_three : (∑ current ∈ coefficients.support, coefficients current ^ 2) = 3) :
    ∃ first second : index, first ≠ second ∧ first ≠ principal ∧ second ≠ principal ∧
      (coefficients first = 1 ∨ coefficients first = -1) ∧
      (coefficients second = 1 ∨ coefficients second = -1) ∧
      coefficients = Finsupp.single principal 1 + Finsupp.single first (coefficients first) +
        Finsupp.single second (coefficients second) := by
  classical
  obtain ⟨first, second, distinct, first_distinct, second_distinct, first_sign, second_sign, support_eq⟩ :=
    exists_two_signed_coefficients coefficients principal principal_one norm_three
  refine ⟨first, second, distinct, first_distinct, second_distinct, first_sign, second_sign, ?_⟩
  ext current
  by_cases current_principal : current = principal
  · subst current
    simp [principal_one, first_distinct, second_distinct, Ne.symm]
  · by_cases current_first : current = first
    · subst current
      simp [first_distinct, distinct]
    · by_cases current_second : current = second
      · subst current
        simp [second_distinct, distinct, Ne.symm]
      · have zero_coefficient : coefficients current = 0 := by
          by_contra nonzero
          have membership := Finsupp.mem_support_iff.mpr nonzero
          rw [support_eq] at membership
          simp [current_principal, current_first, current_second] at membership
        simp [current_principal, current_first, current_second, zero_coefficient]

end CFSG.OrderReductions.NormThreeCoefficients
