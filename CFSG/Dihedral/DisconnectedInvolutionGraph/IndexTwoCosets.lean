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
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem index_two_outside_quotient_equal (subgroup : Subgroup G)
    (hindex : subgroup.index = 2) (first second : G)
    (hfirst : first ∉ subgroup) (hsecond : second ∉ subgroup) :
    first * second⁻¹ ∈ subgroup := by
  let _ := Subgroup.normal_of_index_eq_two hindex
  let quotient := QuotientGroup.mk' subgroup
  have hcard : Nat.card (G ⧸ subgroup) = 2 := hindex
  have hfirstNe : quotient first ≠ 1 := by
    intro hone
    exact hfirst ((QuotientGroup.eq_one_iff first).mp hone)
  have hsecondNe : quotient second ≠ 1 := by
    intro hone
    exact hsecond ((QuotientGroup.eq_one_iff second).mp hone)
  obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : G ⧸ subgroup)).mp hcard
  have hequal : quotient first = quotient second :=
    (hunique (quotient first) hfirstNe).trans (hunique (quotient second) hsecondNe).symm
  apply (QuotientGroup.eq_one_iff (first * second⁻¹)).mp
  change quotient (first * second⁻¹) = 1
  rw [map_mul, map_inv, hequal, mul_inv_cancel]

omit [Finite G] in
theorem cyclic_index_two_outside_square_central (subgroup : Subgroup G)
    (hindex : subgroup.index = 2) (hcyclic : IsCyclic subgroup)
    (element : G) (houtside : element ∉ subgroup) :
    element ^ 2 ∈ Subgroup.center G := by
  let _ := hcyclic
  let _ := Subgroup.normal_of_index_eq_two hindex
  have hsquareMem : element ^ 2 ∈ subgroup := by
    simpa only [hindex] using subgroup.pow_index_mem element
  have hcommuteSubgroup : ∀ actor ∈ subgroup, Commute actor (element ^ 2) := by
    intro actor hmem
    exact congrArg (fun other : subgroup => other.val)
      (mul_comm' (⟨actor, hmem⟩ : subgroup) ⟨element ^ 2, hsquareMem⟩)
  apply Subgroup.mem_center_iff.mpr
  intro actor
  by_cases hmem : actor ∈ subgroup
  · exact hcommuteSubgroup actor hmem
  · have hdifference := index_two_outside_quotient_equal subgroup hindex actor element hmem houtside
    have hcommute := (hcommuteSubgroup (actor * element⁻¹) hdifference).mul_left
      (Commute.self_pow element 2)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcommute.eq

end CFSG.DisconnectedInvolutionGraph.Helpers
