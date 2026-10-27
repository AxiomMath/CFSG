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

namespace CFSG.QuasithinUnique.Unc25K1
open scoped MatrixGroups

abbrev S3 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)

structure R9 where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
  d : ZMod 3
  e : ZMod 3
  f : ZMod 3
  g : ZMod 3
  h : ZMod 3
  i : ZMod 3
  deriving DecidableEq

@[expose] def rmul (x y : R9) : R9 :=
  ⟨x.a*y.a+x.b*y.d+x.c*y.g, x.a*y.b+x.b*y.e+x.c*y.h, x.a*y.c+x.b*y.f+x.c*y.i,
   x.d*y.a+x.e*y.d+x.f*y.g, x.d*y.b+x.e*y.e+x.f*y.h, x.d*y.c+x.e*y.f+x.f*y.i,
   x.g*y.a+x.h*y.d+x.i*y.g, x.g*y.b+x.h*y.e+x.i*y.h, x.g*y.c+x.h*y.f+x.i*y.i⟩

@[expose] def rone : R9 := ⟨1,0,0,0,1,0,0,0,1⟩

@[expose] def rdet (x : R9) : ZMod 3 :=
  x.a*x.e*x.i - x.a*x.f*x.h - x.b*x.d*x.i + x.b*x.f*x.g + x.c*x.d*x.h - x.c*x.e*x.g

@[expose] def vals : List (ZMod 3) := [0, 1, 2]

@[expose] def rawAll : List R9 :=
  vals.flatMap fun a => vals.flatMap fun b => vals.flatMap fun c =>
  vals.flatMap fun d => vals.flatMap fun e => vals.flatMap fun f =>
  vals.flatMap fun g => vals.flatMap fun h => vals.map fun i => ⟨a,b,c,d,e,f,g,h,i⟩

@[expose] def rawList : List R9 := rawAll.filter fun r => rdet r == 1

@[expose] def rr (x : S3) : R9 :=
  ⟨x.1 0 0, x.1 0 1, x.1 0 2, x.1 1 0, x.1 1 1, x.1 1 2, x.1 2 0, x.1 2 1, x.1 2 2⟩

@[expose] def u0S : S3 := ⟨!![1,0,0;0,2,0;0,0,2], by decide⟩

@[expose] def aS : S3 := ⟨!![1,0,0;0,0,1;0,2,2], by decide⟩

@[expose] def bS : S3 := ⟨!![1,0,0;0,0,2;0,1,2], by decide⟩

@[expose] def t3S : S3 := ⟨!![1,0,0;0,1,0;0,1,1], by decide⟩

@[expose] def t4S : S3 := ⟨!![1,0,0;0,1,0;0,2,1], by decide⟩

@[expose] def t5S : S3 := ⟨!![1,0,0;0,1,1;0,0,1], by decide⟩

@[expose] def t6S : S3 := ⟨!![1,0,0;0,1,2;0,0,1], by decide⟩

@[expose] def t7S : S3 := ⟨!![1,0,0;0,2,1;0,2,0], by decide⟩

@[expose] def t8S : S3 := ⟨!![1,0,0;0,2,2;0,1,0], by decide⟩

@[expose] def TlS : List S3 := [1, aS, bS, t3S, t4S, t5S, t6S, t7S, t8S]

@[expose] def WsS : List (List Bool) :=
  [[], [false], [true], [false, false, true, false], [true, true, false, true],
    [true, false, true, true], [false, true, false, false], [true, true], [false, false]]

@[expose] def PlS : List (S3 × S3) :=
  (TlS.product TlS).filter
    (fun p => decide (p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ (p.1 * p.2) ^ 2 ≠ 1 ∧ (p.1 * p.2) ^ 4 = 1))

end CFSG.QuasithinUnique.Unc25K1
