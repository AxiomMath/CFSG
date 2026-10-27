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

namespace CFSG.QuasithinUnique.Unc25K1.Six
open Equiv

abbrev P6 : Type := Equiv.Perm (Fin 6)

@[expose] def perm6 (cs : List (List (Fin 6))) : P6 := (cs.map List.formPerm).prod

structure R6 where
  a : Fin 6
  b : Fin 6
  c : Fin 6
  d : Fin 6
  e : Fin 6
  f : Fin 6
  deriving @[expose] DecidableEq

end CFSG.QuasithinUnique.Unc25K1.Six

namespace CFSG.QuasithinUnique.Unc25K1.Six.R6
open Equiv

@[expose] def get (x : R6) : Fin 6 → Fin 6
  | 0 => x.a
  | 1 => x.b
  | 2 => x.c
  | 3 => x.d
  | 4 => x.e
  | 5 => x.f

@[expose] def mul (x y : R6) : R6 := ⟨x.get y.a, x.get y.b, x.get y.c, x.get y.d, x.get y.e, x.get y.f⟩

@[expose] def one : R6 := ⟨0, 1, 2, 3, 4, 5⟩

instance : Mul R6 := ⟨mul⟩

instance : One R6 := ⟨one⟩

@[expose] def enc (σ : P6) : R6 := ⟨σ 0, σ 1, σ 2, σ 3, σ 4, σ 5⟩

end CFSG.QuasithinUnique.Unc25K1.Six.R6

namespace CFSG.QuasithinUnique.Unc25K1.Six
open Equiv

@[expose] def stepL {R : Type*} [Mul R] [DecidableEq R] (gens L : List R) : List R :=
  L ++ ((L.flatMap fun x => gens.map fun g => x * g).filter fun y => decide (y ∉ L)).dedup

@[expose] def iterL {R : Type*} [One R] [Mul R] [DecidableEq R] (gens : List R) : ℕ → List R
  | 0 => [1]
  | n + 1 => stepL gens (iterL gens n)

@[expose] def closedB {R : Type*} [One R] [Mul R] [DecidableEq R] (gens L : List R) : Bool :=
  decide ((1 : R) ∈ L) && L.all fun x => gens.all fun g => decide (x * g ∈ L)

@[expose] def d0Gens : List P6 := [perm6 [[0, 1, 2, 3], [4, 5]], perm6 [[0, 2], [4, 5]]]

@[expose] def saGens : List P6 := d0Gens ++ [perm6 [[2, 3], [4, 5]]]

@[expose] def sbGens : List P6 := d0Gens ++ [perm6 [[1, 4], [3, 5]]]

@[expose] def repsP : List P6 :=
  [perm6 [[0, 4, 3]], perm6 [[0, 2], [1, 4]], perm6 [[0, 2, 4, 5, 1]], perm6 [[0, 3], [1, 5, 2, 4]],
    perm6 [[1, 4, 3, 2, 5]], perm6 [[0, 3, 4, 2], [1, 5]]]

@[expose] def d0L : List R6 := iterL (d0Gens.map R6.enc) 4

@[expose] def saL : List R6 := iterL (saGens.map R6.enc) 5

@[expose] def sbL : List R6 := iterL (sbGens.map R6.enc) 5

@[expose] def repLs : List (List R6) := repsP.map fun r => iterL ((d0Gens ++ [r]).map R6.enc) 11

@[expose] def conjIn (τ : R6) (L : List R6) (g : R6) : Bool := L.any fun y => decide (τ * g = y * τ)

end CFSG.QuasithinUnique.Unc25K1.Six
