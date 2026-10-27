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
public import Mathlib.Topology.Sheaves.Init

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem p_group_invariant_sum_fixedPoints {ring group points : Type*}
    [CommRing ring] [Group group] [Finite group] [MulAction group points] [Fintype points]
    (prime : ℕ) [Fact prime.Prime] [CharP ring prime] (hgroup : IsPGroup prime group)
    (weight : points → ring) (hinvariant : ∀ (element : group) (point : points),
      weight (element • point) = weight point) :
    ∑ point, weight point =
      ∑ point, if point ∈ MulAction.fixedPoints group points then weight point else 0 := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient group points)
  let : ∀ orbit : MulAction.orbitRel.Quotient group points,
      Fintype (MulAction.orbit group orbit.out) := fun _ => Fintype.ofFinite _
  let equivalence := MulAction.selfEquivSigmaOrbits group points
  have hreindex : ∀ function : points → ring,
      (∑ point, function point) =
        ∑ orbit : MulAction.orbitRel.Quotient group points,
          ∑ member : MulAction.orbit group orbit.out, function member.val := by
    intro function
    calc
      _ = ∑ coordinate : (orbit : MulAction.orbitRel.Quotient group points) ×
          MulAction.orbit group orbit.out, function coordinate.2.val :=
        Fintype.sum_equiv equivalence function (fun coordinate => function coordinate.2.val)
          (fun _ => rfl)
      _ = _ := Fintype.sum_sigma _
  rw [hreindex weight, hreindex (fun point =>
    if point ∈ MulAction.fixedPoints group points then weight point else 0)]
  apply Finset.sum_congr rfl
  intro orbit _
  have hconstant : ∀ member : MulAction.orbit group orbit.out, weight member.val = weight orbit.out := by
    intro member
    obtain ⟨element, hequal⟩ := MulAction.mem_orbit_iff.mp member.property
    rw [← hequal, hinvariant]
  by_cases hfixed : orbit.out ∈ MulAction.fixedPoints group points
  · apply Finset.sum_congr rfl
    intro member _
    obtain ⟨element, hequal⟩ := MulAction.mem_orbit_iff.mp member.property
    have heq : member.val = orbit.out := hequal.symm.trans (MulAction.mem_fixedPoints.mp hfixed element)
    rw [heq, ite_eq_left hfixed]
  · have hnone : ∀ member : MulAction.orbit group orbit.out,
        member.val ∉ MulAction.fixedPoints group points := by
      intro member hmember
      obtain ⟨element, hequal⟩ := MulAction.mem_orbit_iff.mp member.property
      have heq : member.val = orbit.out := by
        have hfix := MulAction.mem_fixedPoints.mp hmember element⁻¹
        rw [← hequal, inv_smul_smul] at hfix
        exact hequal.symm.trans hfix.symm
      exact hfixed (heq ▸ hmember)
    simp only [hconstant, hnone, ite_false, Finset.sum_const_zero, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    obtain ⟨exponent, hcard⟩ := hgroup.card_orbit orbit.out
    have hnonzero : exponent ≠ 0 := by
      intro hequal
      have hcardone : Nat.card (MulAction.orbit group orbit.out) = 1 := by
        rw [hcard, hequal, pow_zero]
      have hsubsingleton := (Nat.card_eq_one_iff_unique.mp hcardone).1
      apply hfixed
      rw [MulAction.mem_fixedPoints]
      intro element
      exact congrArg Subtype.val (hsubsingleton.elim
        (⟨element • orbit.out, MulAction.mem_orbit orbit.out element⟩ : MulAction.orbit group orbit.out)
        ⟨orbit.out, MulAction.mem_orbit_self orbit.out⟩)
    have hdvd : prime ∣ Fintype.card (MulAction.orbit group orbit.out) := by
      rw [← Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self prime hnonzero
    exact (congrArg (fun scalar : ring => scalar * weight orbit.out)
      (CharP.cast_eq_zero_iff ring prime _ |>.mpr hdvd)).trans (zero_mul _)

end CFSG.TwoRankLowerBound.Helpers
