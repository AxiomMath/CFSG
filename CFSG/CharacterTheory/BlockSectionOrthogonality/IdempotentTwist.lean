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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.BlockSectionOrthogonality.Helpers

theorem idempotent_intertwiner {ring : Type*} [Ring ring]
    (left right : ring) (hleft : left * left = left) (hright : right * right = right) :
    (left * right + (1 - left) * (1 - right)) * right =
      left * (left * right + (1 - left) * (1 - right)) := by
  noncomm_ring [hleft, hright]
  rw [← mul_assoc left left right, hleft]
  module

theorem idempotent_intertwiner_eq_one {ring : Type*} [Ring ring]
    (idempotent : ring) (hidempotent : idempotent * idempotent = idempotent) :
    idempotent * idempotent + (1 - idempotent) * (1 - idempotent) = 1 := by
  noncomm_ring [hidempotent]

theorem matrix_isUnit_of_residue_eq_one {ring : Type*} [CommRing ring] [IsLocalRing ring]
    {index : Type*} [Fintype index] [DecidableEq index]
    (matrix : Matrix index index ring)
    (hresidue : (IsLocalRing.residue ring).mapMatrix matrix = 1) : IsUnit matrix := by
  apply (Matrix.isUnit_iff_isUnit_det matrix).mpr
  apply (IsLocalRing.residue_ne_zero_iff_isUnit matrix.det).mp
  rw [RingHom.map_det, hresidue, Matrix.det_one]
  exact one_ne_zero

theorem equivariant_idempotent_congr_trace {ring : Type*} [CommRing ring] [IsLocalRing ring]
    {index : Type*} [Fintype index] [DecidableEq index]
    (left right permutation : Matrix index index ring)
    (hleft : left * left = left) (hright : right * right = right)
    (hleftCommute : left * permutation = permutation * left)
    (hrightCommute : right * permutation = permutation * right)
    (hresidue : (IsLocalRing.residue ring).mapMatrix left =
      (IsLocalRing.residue ring).mapMatrix right) :
    (left * permutation).trace = (right * permutation).trace := by
  let intertwiner := left * right + (1 - left) * (1 - right)
  have hResidueIntertwiner : (IsLocalRing.residue ring).mapMatrix intertwiner = 1 := by
    dsimp [intertwiner]
    simp only [map_add, map_mul, map_sub, map_one, hresidue]
    apply idempotent_intertwiner_eq_one
    rw [← map_mul, hright]
  have hUnit := matrix_isUnit_of_residue_eq_one intertwiner hResidueIntertwiner
  let unit := hUnit.unit
  have hUnitValue : (unit : Matrix index index ring) = intertwiner := hUnit.unit_spec
  have hIntertwines : intertwiner * right = left * intertwiner :=
    idempotent_intertwiner left right hleft hright
  have hCommute : intertwiner * permutation = permutation * intertwiner := by
    dsimp [intertwiner]
    noncomm_ring [hleftCommute, hrightCommute]
    rw [← mul_assoc left permutation right, hleftCommute, mul_assoc]
    module
  have hProduct : intertwiner * (right * permutation) =
      (left * permutation) * intertwiner := by
    rw [← mul_assoc, hIntertwines, mul_assoc, hCommute, ← mul_assoc]
  have hConjugate : (unit : Matrix index index ring) * (right * permutation) *
      (↑unit⁻¹ : Matrix index index ring) = left * permutation := by
    rw [hUnitValue, hProduct, ← hUnitValue, mul_assoc, Units.mul_inv, mul_one]
  rw [← hConjugate, Matrix.trace_mul_cycle, ← mul_assoc, Units.inv_mul, one_mul]

theorem equivariant_idempotent_twist_trace_zero
    {ring : Type*} [CommRing ring] [IsLocalRing ring] [IsDomain ring]
    {index : Type*} [Fintype index] [DecidableEq index]
    (idempotent permutation : Matrix index index ring)
    (hidempotent : idempotent * idempotent = idempotent)
    (hcommute : idempotent * permutation = permutation * idempotent)
    (twist : (Matrix index index ring)ˣ) (scalar : ring)
    (hscalar : scalar ≠ 1)
    (hTwistPermutation : (twist : Matrix index index ring) * permutation *
      (↑twist⁻¹ : Matrix index index ring) = scalar • permutation)
    (hTwistResidue : (IsLocalRing.residue ring).mapMatrix
      (twist : Matrix index index ring) = 1) :
    (idempotent * permutation).trace = 0 := by
  let conjugate := (↑twist⁻¹ : Matrix index index ring) * idempotent *
    (twist : Matrix index index ring)
  have hConjugateIdempotent : conjugate * conjugate = conjugate := by
    dsimp [conjugate]
    calc
      _ = (↑twist⁻¹ : Matrix index index ring) * (idempotent * idempotent) *
          (twist : Matrix index index ring) := by
        simp only [mul_assoc, ← mul_assoc (twist : Matrix index index ring)
          (↑twist⁻¹ : Matrix index index ring), Units.mul_inv, one_mul]
      _ = _ := by rw [hidempotent]
  have hInverseResidue : (IsLocalRing.residue ring).mapMatrix
      (↑twist⁻¹ : Matrix index index ring) = 1 := by
    have hIdentity := congrArg ((IsLocalRing.residue ring).mapMatrix) (Units.mul_inv twist)
    simpa only [map_mul, hTwistResidue, map_one, one_mul] using hIdentity
  have hResidue : (IsLocalRing.residue ring).mapMatrix conjugate =
      (IsLocalRing.residue ring).mapMatrix idempotent := by
    simp only [conjugate, map_mul, hInverseResidue, hTwistResidue, one_mul, mul_one]
  have hTwistMove : (twist : Matrix index index ring) * permutation =
      scalar • permutation * (twist : Matrix index index ring) := by
    have hMove := congrArg (fun matrix => matrix * (twist : Matrix index index ring))
      hTwistPermutation
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hMove
  have hInverseMove : (↑twist⁻¹ : Matrix index index ring) * (scalar • permutation) =
      permutation * (↑twist⁻¹ : Matrix index index ring) := by
    have hMove := congrArg (fun matrix => (↑twist⁻¹ : Matrix index index ring) * matrix)
      hTwistPermutation
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hMove.symm
  have hConjugateCommute : conjugate * permutation = permutation * conjugate := by
    dsimp [conjugate]
    calc
      _ = (↑twist⁻¹ : Matrix index index ring) *
          (idempotent * (scalar • permutation)) * (twist : Matrix index index ring) := by
        rw [mul_assoc, hTwistMove]
        simp only [mul_assoc]
      _ = (↑twist⁻¹ : Matrix index index ring) *
          ((scalar • permutation) * idempotent) * (twist : Matrix index index ring) := by
        rw [mul_smul_comm, hcommute, ← smul_mul_assoc]
      _ = _ := by
        rw [← mul_assoc, hInverseMove]
        simp only [mul_assoc]
  have hTraceEqual := equivariant_idempotent_congr_trace conjugate idempotent permutation
    hConjugateIdempotent hidempotent hConjugateCommute hcommute hResidue
  have hTraceTwist : (conjugate * permutation).trace =
      scalar * (idempotent * permutation).trace := by
    dsimp [conjugate]
    rw [mul_assoc, hTwistMove, ← mul_assoc, mul_smul_comm,
      smul_mul_assoc, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_cycle, ← mul_assoc, Units.mul_inv, one_mul]
  rw [hTraceTwist] at hTraceEqual
  have hProductZero : (scalar - 1) * (idempotent * permutation).trace = 0 := by
    rw [sub_mul, one_mul, hTraceEqual, sub_self]
  exact (mul_eq_zero.mp hProductZero).resolve_left (sub_ne_zero.mpr hscalar)

end CFSG.BlockSectionOrthogonality.Helpers
