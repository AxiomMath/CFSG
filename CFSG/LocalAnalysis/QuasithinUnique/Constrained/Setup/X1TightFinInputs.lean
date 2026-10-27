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

namespace CFSG.QuasithinUnique.Setup.X1.Tight

@[expose] def app5 (f : Nat → Nat) (n : Nat) : Nat :=
  (if n.testBit 0 then f 0 else 0) ^^^ (if n.testBit 1 then f 1 else 0) ^^^
    (if n.testBit 2 then f 2 else 0) ^^^ (if n.testBit 3 then f 3 else 0) ^^^
      (if n.testBit 4 then f 4 else 0)

@[expose] def shiftC (k : Nat) : Nat := 2 ^ ((k + 1) % 5)

@[expose] def dbC (k : Nat) : Nat := 2 ^ ((2 * k) % 5)

@[expose] def rotn : Nat → Nat → Nat
  | 0, n => n
  | m + 1, n => app5 shiftC (rotn m n)

@[expose] def th0C (x y : Nat) (k : Nat) : Nat :=
  if k = 0 then x else if k = 1 then y else if k = 2 then app5 dbC y
  else if k = 3 then app5 dbC (app5 dbC (app5 dbC y)) else app5 dbC (app5 dbC y)

@[expose] def thC (x y : Nat) (i k : Nat) : Nat := rotn i (th0C x y ((k + 5 - i % 5) % 5))

@[expose] def imgCard (f : Nat → Nat) : Nat := ((Finset.range 32).image (app5 f)).card

@[expose] def good (x y : Nat) : Bool :=
  (List.range 5).all (fun k => (thC x y 0 k ^^^ thC x y 1 k ^^^ thC x y 2 k ^^^ thC x y 3 k ^^^
      thC x y 4 k) == 2 ^ k) &&
    (imgCard (th0C x y) == 32) &&
    decide (16 ≤ imgCard (fun k => thC x y 0 k ^^^ thC x y 1 k)) &&
    decide (16 ≤ imgCard (fun k => thC x y 0 k ^^^ thC x y 1 k ^^^ thC x y 2 k ^^^ thC x y 3 k))

@[expose] def dwC (w k : Nat) : Nat := rotn (2 * k) w

@[expose] def cycOK (x : Nat) : Bool :=
  (List.range 32).all fun z => (List.range 32).any fun e => app5 (fun k => rotn k x) e == z

end CFSG.QuasithinUnique.Setup.X1.Tight
