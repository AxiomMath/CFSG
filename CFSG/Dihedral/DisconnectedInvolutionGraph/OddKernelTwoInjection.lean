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

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G K : Type*} [Group G] [Group K]

theorem two_pgroup_odd_kernel_injective (hpgroup : IsPGroup 2 G)
    (hom : G →* K) (hodd : Odd (Nat.card hom.ker)) : Function.Injective hom := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hom.ker_eq_bot_iff.mp
  apply hom.ker.eq_bot_iff_forall.mpr
  intro element hmem
  by_contra hne
  have hdiv := (hpgroup.dvd_orderOf hne).trans (hom.ker.orderOf_dvd_natCard hmem)
  exact hodd.not_two_dvd_nat hdiv

theorem odd_kernel_two_subgroup_injective (hom : G →* K)
    (hodd : Odd (Nat.card hom.ker)) (subgroup : Subgroup G)
    (hpgroup : IsPGroup 2 subgroup) : Function.Injective (hom.comp subgroup.subtype) := by
  let restricted := hom.comp subgroup.subtype
  apply restricted.ker_eq_bot_iff.mp
  apply restricted.ker.eq_bot_iff_forall.mpr
  intro element hmem
  by_contra hne
  have hambientNe : (element : G) ≠ 1 := by
    intro heq
    exact hne (Subtype.ext heq)
  have hdiv : 2 ∣ orderOf (element : G) := by
    rw [Subgroup.orderOf_coe]
    exact hpgroup.dvd_orderOf hne
  exact hodd.not_two_dvd_nat (hdiv.trans (hom.ker.orderOf_dvd_natCard hmem))

end CFSG.DisconnectedInvolutionGraph.Helpers
