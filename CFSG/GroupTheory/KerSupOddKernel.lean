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

namespace CFSG.GroupTheory

theorem map_eq_one_of_sq_eq_one_of_ker_sup_eq_top {Y : Type*} [Group Y] [Finite Y]
    {N : Subgroup Y} [N.Normal] (hodd : Odd (Nat.card N))
    {M : Type*} [Monoid M] (ρ : Y →* M)
    (htop : ρ.ker ⊔ N = ⊤) {y : Y} (hy : y ^ 2 = 1) : ρ y = 1 := by
  obtain ⟨k, hk, n, hn, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp (htop ▸ Subgroup.mem_top y)
  have hρ : ρ (k * n) = ρ n := by rw [map_mul, MonoidHom.mem_ker.mp hk, one_mul]
  have hoddn : Odd (orderOf n) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn)
  have hoddρ : Odd (orderOf (ρ n)) := hoddn.of_dvd_nat (orderOf_map_dvd ρ n)
  have hdvd : orderOf (ρ n) ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← hρ, ← map_pow, hy, map_one]
  rw [hρ]
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hoddρ.coprime_two_right hdvd)

end CFSG.GroupTheory

end
