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
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
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

variable {G : Type*} [Group G]

@[expose] def quaternionCoordinateHom (size : ℕ)
    (coordinates : Multiplicative (ZMod (2 * size)) →* G) (outside : G)
    (hsquare : outside ^ 2 = coordinates (Multiplicative.ofAdd (size : ZMod (2 * size))))
    (hinversion : ∀ coordinate, outside * coordinates coordinate * outside⁻¹ =
      (coordinates coordinate)⁻¹) : QuaternionGroup size →* G := by
  let coordinateMap := fun coordinate : ZMod (2 * size) =>
    coordinates (Multiplicative.ofAdd coordinate)
  have hmapAdd : ∀ first second, coordinateMap (first + second) =
      coordinateMap first * coordinateMap second := by
    intro first second
    exact coordinates.map_mul _ _
  have hmapNeg : ∀ coordinate, coordinateMap (-coordinate) = (coordinateMap coordinate)⁻¹ := by
    intro coordinate
    exact coordinates.map_inv _
  have hmapSub : ∀ first second, coordinateMap (first - second) =
      coordinateMap first * (coordinateMap second)⁻¹ := by
    intro first second
    rw [sub_eq_add_neg, hmapAdd, hmapNeg]
  have hcommute : ∀ first second, Commute (coordinateMap first) (coordinateMap second) := by
    intro first second
    exact (hmapAdd first second).symm.trans ((congrArg coordinateMap (add_comm first second)).trans
      (hmapAdd second first))
  have hpassOutside : ∀ coordinate, coordinateMap coordinate * outside =
      outside * (coordinateMap coordinate)⁻¹ := by
    intro coordinate
    have hequal := hinversion (Multiplicative.ofAdd (-coordinate))
    change outside * coordinateMap (-coordinate) * outside⁻¹ =
      (coordinateMap (-coordinate))⁻¹ at hequal
    rw [hmapNeg, inv_inv] at hequal
    exact (mul_inv_eq_iff_eq_mul.mp hequal).symm
  refine
    { toFun := fun element => match element with
        | QuaternionGroup.a coordinate => coordinateMap coordinate
        | QuaternionGroup.xa coordinate => outside * coordinateMap coordinate
      map_one' := ?_
      map_mul' := ?_ }
  · change coordinateMap 0 = 1
    exact coordinates.map_one
  · intro first second
    cases first with
    | a first =>
      cases second with
      | a second =>
        change coordinateMap (first + second) = coordinateMap first * coordinateMap second
        exact hmapAdd first second
      | xa second =>
        change outside * coordinateMap (second - first) =
          coordinateMap first * (outside * coordinateMap second)
        rw [hmapSub]
        calc
          outside * (coordinateMap second * (coordinateMap first)⁻¹) =
              outside * ((coordinateMap first)⁻¹ * coordinateMap second) := by
            rw [(hcommute first second).inv_left.eq]
          _ = coordinateMap first * (outside * coordinateMap second) := by
            rw [← mul_assoc, ← hpassOutside, mul_assoc]
    | xa first =>
      cases second with
      | a second =>
        change outside * coordinateMap (first + second) =
          outside * coordinateMap first * coordinateMap second
        rw [hmapAdd, mul_assoc]
      | xa second =>
        change coordinateMap ((size : ZMod (2 * size)) + second - first) =
          outside * coordinateMap first * (outside * coordinateMap second)
        rw [hmapSub, hmapAdd]
        rw [← mul_assoc (outside * coordinateMap first), mul_assoc outside
          (coordinateMap first) outside, hpassOutside, ← mul_assoc outside outside,
          ← pow_two outside, hsquare]
        change coordinateMap (size : ZMod (2 * size)) * coordinateMap second *
          (coordinateMap first)⁻¹ =
          coordinateMap (size : ZMod (2 * size)) * (coordinateMap first)⁻¹ * coordinateMap second
        rw [mul_assoc, mul_assoc, (hcommute first second).inv_left]

end CFSG.DisconnectedInvolutionGraph.Helpers
