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

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem orbitQuotientCoordinates_inverse_apply {group points : Type*} [Group group]
    [MulAction group points] (orbit : MulAction.orbitRel.Quotient group points) (element : group) :
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer group points).symm ⟨orbit, element⟩ =
      element • orbit.out := by
  change ((MulAction.orbitEquivQuotientStabilizer group orbit.out).symm
    (element : group ⧸ MulAction.stabilizer group orbit.out)).val = _
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply group orbit.out element

theorem orbitQuotientCoordinates_inverse_equivariant {group points : Type*} [CommGroup group]
    [MulAction group points] (orbit : MulAction.orbitRel.Quotient group points) (element : group)
    (coset : group ⧸ MulAction.stabilizer group orbit.out) :
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer group points).symm
        ⟨orbit, QuotientGroup.mk' (MulAction.stabilizer group orbit.out) element * coset⟩ =
      element • (MulAction.selfEquivSigmaOrbitsQuotientStabilizer group points).symm ⟨orbit, coset⟩ := by
  refine QuotientGroup.induction_on coset ?_
  intro representative
  change (MulAction.selfEquivSigmaOrbitsQuotientStabilizer group points).symm
    ⟨orbit, (QuotientGroup.mk' (MulAction.stabilizer group orbit.out) element) *
      (QuotientGroup.mk' (MulAction.stabilizer group orbit.out) representative)⟩ = _
  rw [← map_mul]
  change (MulAction.selfEquivSigmaOrbitsQuotientStabilizer group points).symm
    ⟨orbit, ((element * representative : group) : group ⧸ MulAction.stabilizer group orbit.out)⟩ = _
  rw [orbitQuotientCoordinates_inverse_apply, orbitQuotientCoordinates_inverse_apply, mul_smul]

end CFSG.TwoRankLowerBound.Helpers
