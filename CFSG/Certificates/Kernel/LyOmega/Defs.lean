module

public import Certificates.Data.Kernel.LyOmega.Tree
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

namespace CFSG.KS.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL

@[expose] def ent (w S X i j : ℕ) : ZMod 5 := ((X / 2 ^ (S * i + w * j) % 2 ^ w : ℕ) : ZMod 5)

@[expose] def blkM (X : ℕ) : Matrix (Fin 7) (Fin 111) (ZMod 5) := fun i j => ent 12 1332 X i j

@[expose] def bigM (X : ℕ) : Matrix (Fin 111) (Fin 111) (ZMod 5) := fun i j => ent 12 1332 X i j

@[expose] def smM (X : ℕ) : Matrix (Fin 7) (Fin 7) (ZMod 5) := fun i j => ent 11 77 X i j

@[expose] def kM (X : ℕ) : Matrix (Fin 49) (Fin 49) (ZMod 5) := fun i j => ent 11 539 X i j

@[expose] def vec49 (X : ℕ) : Fin 49 → ZMod 5 := fun t => ent 11 0 X 0 t

@[expose] def LCanon (w r c X : ℕ) : Prop :=
  X < 2 ^ (w * c * r) ∧ ∀ i < r, ∀ j < c, X / 2 ^ (w * c * i + w * j) % 2 ^ w < 5

@[expose] def rowSpan (X : ℕ) : Submodule (ZMod 5) (Fin 111 → ZMod 5) :=
  Submodule.span (ZMod 5) (Set.range (blkM X))

@[expose] def lastCols (M : Matrix (Fin 7) (Fin 111) (ZMod 5)) : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  fun i j => M i ⟨104 + j.val, by omega⟩

@[expose] def firstCols (M : Matrix (Fin 7) (Fin 111) (ZMod 5)) : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  fun i j => M i ⟨j.val, by omega⟩

