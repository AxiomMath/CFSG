module

public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.RankThree.PartOne.KS.RuFiveData
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

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native
open CFSG.RankThree.PartOne

@[expose] def signedWordA (n : ℕ) (gs : Array (Array ℕ)) : List (ℕ × Bool) → Array ℕ
  | [] => idA n
  | l :: w => compA n (if l.2 then gs[l.1]! else invCand n gs[l.1]!) (signedWordA n gs w)

@[expose] def ruFiveLinesCheck : Bool :=
  commA 4060 ruFiveLines[0]! ruFiveLines[1]! &&
    allLt 31 fun j => ruFiveRec.getD j 0 % 31 != 0 ||
      !commA 4060 ruFiveLines[j]! ruFiveLines[1]! || j == 0

@[expose] def q8WordI : List (ℕ × Bool) := [(2, true)]

@[expose] def q8WordJ : List (ℕ × Bool) :=
  [(1, true), (2, false), (1, false), (2, false), (1, true), (0, true)]

@[expose] def ruFiveQ8Check : Bool :=
  validA 4060 (signedWordA 4060 ruFiveC0Gens q8WordI) &&
    validA 4060 (signedWordA 4060 ruFiveC0Gens q8WordJ) &&
    eqA 4060 (powArr 4060 (signedWordA 4060 ruFiveC0Gens q8WordI) 4) (idA 4060) &&
    !eqA 4060 (powArr 4060 (signedWordA 4060 ruFiveC0Gens q8WordI) 2) (idA 4060) &&
    eqA 4060 (powArr 4060 (signedWordA 4060 ruFiveC0Gens q8WordI) 2)
      (powArr 4060 (signedWordA 4060 ruFiveC0Gens q8WordJ) 2) &&
    eqA 4060 (compA 4060 (compA 4060 (signedWordA 4060 ruFiveC0Gens q8WordJ)
      (signedWordA 4060 ruFiveC0Gens q8WordI))
      (invCand 4060 (signedWordA 4060 ruFiveC0Gens q8WordJ)))
      (invCand 4060 (signedWordA 4060 ruFiveC0Gens q8WordI))

end CFSG.EvenSporadicStandard.RuStd.S2
