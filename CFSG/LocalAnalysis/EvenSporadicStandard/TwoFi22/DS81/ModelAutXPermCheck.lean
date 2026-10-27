module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXData
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
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

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore

set_option compiler.extract_closed false

@[expose] def axLetterTab (G Ginv : Array (Array Nat)) (l : Nat × Bool) : Array Nat :=
  if l.2 then Ginv[l.1]! else G[l.1]!

@[expose] def axWordTab (G Ginv : Array (Array Nat)) (w : List (Nat × Bool)) : Array Nat :=
  w.foldr (fun l acc => compA 3510 (axLetterTab G Ginv l) acc) (idA 3510)

@[expose] def axPhiTab (B : Array (Array Nat)) (m : Nat) : Array Nat :=
  (List.range 10).foldr (fun i P => if m.testBit i then compA 3510 B[i]! P else P) (idA 3510)

@[expose] def axPermCheckT (G Ginv : Array (Array Nat)) (words : Array (List (Nat × Bool)))
    (gc : Array (Array Nat)) : Bool :=
  let B : Array (Array Nat) := words.map (axWordTab G Ginv)
  let imgs : Array Nat := (Array.range 1024).map fun m => (axPhiTab B m)[0]!
  decide (G.size = 10) && decide (Ginv.size = 10) && decide (words.size = 10) &&
    (List.range 10).all (fun k => isInvA 3510 G[k]! Ginv[k]!) &&
    words.all (fun w => w.all fun l => decide (l.1 < 9)) &&
    (List.range 10).all (fun i => eqA 3510 (compA 3510 B[i]! B[i]!) (idA 3510)) &&
    (List.range 10).all (fun i => (List.range 10).all fun j =>
      eqA 3510 (compA 3510 B[i]! B[j]!) (compA 3510 B[j]! B[i]!)) &&
    (List.range 10).all (fun k => (List.range 10).all fun i =>
      eqA 3510 (compA 3510 G[k]! B[i]!) (compA 3510 (axPhiTab B (gc[k]!)[i]!) G[k]!)) &&
    (List.range 1024).all fun m => (List.range m).all fun m' => imgs[m]! != imgs[m']!

@[expose] def axPermCertificate : Bool :=
  let G := (Array.range 10).map fun k => fi22ExtArr (11 + k)
  axPermCheckT G (G.map (invCand 3510)) axBasWords axGc

end CFSG.EvenSporadicStandard.TwoFi22.DS81
