module

public import Certificates.Data.CFSGNative.MonsterAxis.Fi23Sp8
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.Fi23P

open CFSG.Monster.Existence.Fi23Sp8.Native

@[expose] def tauV (a x : Nat) : Nat := x ^^^ (if beta a x then a else 0)

@[expose] def pairT (u v i : Nat) : Bool :=
  xor (u.testBit i && v.testBit (i + 4)) (u.testBit (i + 4) && v.testBit i)

theorem beta_eq (u v : Nat) : beta u v =
    xor (xor (pairT u v 0) (pairT u v 1)) (xor (pairT u v 2) (pairT u v 3)) := rfl

theorem pairT_xor_left (u w v i : Nat) : pairT (u ^^^ w) v i = xor (pairT u v i) (pairT w v i) := by
  unfold pairT
  rw [Nat.testBit_xor, Nat.testBit_xor]
  cases u.testBit i <;> cases w.testBit i <;> cases u.testBit (i + 4) <;>
    cases w.testBit (i + 4) <;> cases v.testBit i <;> cases v.testBit (i + 4) <;> rfl

theorem pairT_comm (u v i : Nat) : pairT u v i = pairT v u i := by
  unfold pairT
  cases u.testBit i <;> cases u.testBit (i + 4) <;> cases v.testBit i <;>
    cases v.testBit (i + 4) <;> rfl

theorem pairT_self (u i : Nat) : pairT u u i = false := by
  unfold pairT
  cases u.testBit i <;> cases u.testBit (i + 4) <;> rfl

theorem xor8 (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    xor (xor (xor a0 b0) (xor a1 b1)) (xor (xor a2 b2) (xor a3 b3)) =
      xor (xor (xor a0 a1) (xor a2 a3)) (xor (xor b0 b1) (xor b2 b3)) := by
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

theorem beta_xor_left (u w v : Nat) : beta (u ^^^ w) v = (beta u v ^^ beta w v) := by
  rw [beta_eq, beta_eq u, beta_eq w, pairT_xor_left, pairT_xor_left, pairT_xor_left,
    pairT_xor_left, xor8]

theorem beta_comm (u v : Nat) : beta u v = beta v u := by
  rw [beta_eq, beta_eq v, pairT_comm u v 0, pairT_comm u v 1, pairT_comm u v 2, pairT_comm u v 3]

theorem beta_xor_right (u v w : Nat) : beta u (v ^^^ w) = (beta u v ^^ beta u w) := by
  rw [beta_comm, beta_xor_left, beta_comm v, beta_comm w]

theorem beta_self (u : Nat) : beta u u = false := by
  rw [beta_eq, pairT_self, pairT_self, pairT_self, pairT_self]
  rfl

theorem beta_zero_left (v : Nat) : beta 0 v = false := by
  simp [beta]

theorem beta_sel_left (c : Bool) (a v : Nat) : beta (if c then a else 0) v = (c && beta a v) := by
  cases c <;> simp [beta_zero_left]

theorem beta_sel_right (c : Bool) (a v : Nat) : beta v (if c then a else 0) = (c && beta v a) := by
  rw [beta_comm, beta_sel_left, beta_comm]

theorem tauV_conj (a b x : Nat) : tauV a (tauV b (tauV a x)) = tauV (tauV a b) x := by
  unfold tauV
  simp only [beta_xor_right, beta_xor_left, beta_sel_right, beta_sel_left, beta_self,
    beta_comm b a, beta_comm x a, beta_comm x b, Bool.and_false, Bool.xor_false]
  cases beta a x <;> cases beta a b <;> cases beta b x
  all_goals
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.xor_true, Bool.not_true,
      Bool.not_false, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, ite_true, ite_false, Nat.testBit_xor, Nat.zero_testBit]
    all_goals cases x.testBit j <;> cases a.testBit j <;> cases b.testBit j <;> rfl

end CFSG.KC.Fi23P

end
