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
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
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

namespace CFSG.LargeExtraspecial.O62

open Polynomial

theorem irreducible_cyclotomic_nine : Irreducible (cyclotomic 9 (ZMod 2)) := by
  have hpn : ¬ 2 ∣ 9 := by norm_num
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree hpn dvd_rfl ?_
  rw [natDegree_cyclotomic]
  have h6 : orderOf (ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 9)) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    exact ⟨by decide, by decide⟩
  rw [h6]
  decide

theorem matrix_pow_three_eq_one_of_pow_nine (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h : A ^ 9 = 1) : A ^ 3 = 1 := by
  set μ := minpoly (ZMod 2) A
  have hμ0 : μ ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral A)
  have hdeg : μ.natDegree ≤ 4 := by
    have h1 := natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly A) (Matrix.charpoly_monic A).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
  have h9 : μ ∣ X ^ 9 - 1 := minpoly.dvd (ZMod 2) A (by simp [h])
  have hfac : (X ^ 9 - 1 : (ZMod 2)[X]) = (X ^ 3 - 1) * cyclotomic 9 (ZMod 2) := by
    have := cyclotomic_prime_pow_mul_X_pow_sub_one (ZMod 2) 3 1
    rw [mul_comm] at this
    norm_num at this
    exact this.symm
  have hcop : IsCoprime (cyclotomic 9 (ZMod 2)) μ := by
    refine (irreducible_cyclotomic_nine.coprime_iff_not_dvd).mpr fun hd => ?_
    have h1 := natDegree_le_of_dvd hd hμ0
    rw [natDegree_cyclotomic] at h1
    have h2 : Nat.totient 9 = 6 := by decide
    omega
  have h3 : μ ∣ X ^ 3 - 1 := hcop.symm.dvd_of_dvd_mul_right (by rw [← hfac]; exact h9)
  obtain ⟨r, hr⟩ := h3
  have h4 : aeval A (X ^ 3 - 1 : (ZMod 2)[X]) = 0 := by
    rw [hr, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h4

theorem SL4.pow_three_eq_one_of_pow_nine (A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (h : A ^ 9 = 1) : A ^ 3 = 1 := by
  have h' : (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 9 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact matrix_pow_three_eq_one_of_pow_nine _ h'

end CFSG.LargeExtraspecial.O62
