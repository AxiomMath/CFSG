
module

public import CFSG.Certificates.Kernel.Th.Gen.Seed
import CFSG.Certificates.Kernel.Th.SoundnessGenBase
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

@[expose] public section

namespace CFSG.KC.Th.Soundness

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier
  Pointwise CFSG.KC.Th.Gen

theorem seed_sound (D : SeedData) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : seedChk D = true) :
    let A := Native.rowsOf Native.seedA
    let B := Native.rowsOf Native.seedB
    Native.eqRows (Native.mulRows A A) Native.idRows = true ∧
      Native.eqRows (Native.mulRows (Native.mulRows B B) B) Native.idRows = true ∧
      Native.eqRows (Native.mulRows (Native.mulRows (Native.transposeRows A) Native.fcRows) A)
        Native.fcRows = true ∧
      Native.eqRows (Native.mulRows (Native.mulRows (Native.transposeRows B) Native.fcRows) B)
        Native.fcRows = true :=
  seed_sound_gen _ _ D _hA _hB _h

end CFSG.KC.Th.Soundness
