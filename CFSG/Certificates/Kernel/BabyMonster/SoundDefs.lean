module

public import CFSG.Certificates.Kernel.BabyMonster.F2
public import Certificates.Data.Kernel.YModel.Text
public import Certificates.Data.Kernel.BSeed.Seed
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

namespace CFSG.KC.BM

open CFSG.KC.YModel CFSG.KC.BSeed

@[expose] noncomputable def stripMat (S : List Nat) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  fun i j => if (lget S (i.val / 64)).testBit (64 * j.val + i.val % 64) then 1 else 0

inductive AllStrips (Ws : List (List Nat)) : List Nat → List Nat → Prop
  | nil : AllStrips Ws [] []
  | cons (a c : Nat) (as cs : List Nat) :
      Nat.beq (mulW Ws a) c = true → AllStrips Ws as cs → AllStrips Ws (a :: as) (c :: cs)

inductive AllBlocks : List (List Nat) → List Nat → Nat → Prop
  | nil (s : Nat) : AllBlocks [] [] s
  | cons (blk : List Nat) (T s : Nat) (R : List (List Nat)) (S : List Nat) :
      blockOK blk T s = true → AllBlocks R S (Nat.succ s) → AllBlocks (blk :: R) (T :: S) s

@[expose] noncomputable def idStrips : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun k ih acc => ih (List.cons (idS k) acc)) (nat_lit 69) List.nil

end CFSG.KC.BM

end
