module

public import CFSG.GF2Type.Widths1112.Co2Module.Inputs
public import CFSG.GF2Type.Widths1112.Co2Module.Matrices
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

namespace CFSG.GF2Type.Widths1112.Co2Module

open CFSG.GF2W1112

@[expose] def thetaCode (c : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun a b => (((c >>> (2 * a.val + b.val)) % 2 : ℕ) : ZMod 2)

@[expose] def uXOf (θ : Matrix (Fin 2) (Fin 2) (ZMod 2)) (k : Fin 8) :
    Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Xfin θ (uSigma k) (cfTab uW1 uV0 (uU k))

@[expose] def uX0 (s : Fin 2) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  uXOf (thetaCode (w12UThetaCodes.getD s.val 0)) (iN s)

end CFSG.GF2Type.Widths1112.Co2Module
