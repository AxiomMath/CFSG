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
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.CGT.M24R

abbrev M24Word : Type := List (Fin 11 × Bool)

@[expose] def letX (i : Fin 6) : Fin 11 := ⟨i.val, by omega⟩

@[expose] def letT (j : Fin 4) : Fin 11 := ⟨6 + j.val, by omega⟩

@[expose] def letG : Fin 11 := 10

@[expose] def evalW {H : Type*} [Group H] (e : Fin 11 → H) (w : M24Word) : H :=
  FreeGroup.lift e (FreeGroup.mk w)

@[expose] def invW (w : M24Word) : M24Word := w.reverse.map fun p => (p.1, !p.2)

@[expose] def liftW10 (w : List (Fin 10 × Bool)) : M24Word :=
  w.map fun p => (Fin.castSucc p.1, p.2)

section Eval

variable {H : Type*} [Group H] (e : Fin 11 → H)

@[simp] theorem evalW_nil : evalW e [] = 1 := map_one _

theorem evalW_cons (l : Fin 11 × Bool) (w : M24Word) :
    evalW e (l :: w) = (if l.2 then e l.1 else (e l.1)⁻¹) * evalW e w := by
  unfold evalW
  rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
  obtain ⟨i, b⟩ := l
  cases b
  · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
      FreeGroup.lift_apply_of]
    rfl
  · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
    rfl

@[simp] theorem evalW_cons_true (i : Fin 11) (w : M24Word) :
    evalW e ((i, true) :: w) = e i * evalW e w := evalW_cons e _ w

@[simp] theorem evalW_cons_false (i : Fin 11) (w : M24Word) :
    evalW e ((i, false) :: w) = (e i)⁻¹ * evalW e w := evalW_cons e _ w

theorem evalW_append (w w' : M24Word) : evalW e (w ++ w') = evalW e w * evalW e w' := by
  unfold evalW
  rw [← FreeGroup.mul_mk, map_mul]

theorem evalW_invW (w : M24Word) : evalW e (invW w) = (evalW e w)⁻¹ := by
  induction w with
  | nil => simp [invW]
  | cons l w ih =>
    have h : invW (l :: w) = invW w ++ [(l.1, !l.2)] := by simp [invW]
    rw [h, evalW_append, ih, evalW_cons, evalW_cons, evalW_nil, mul_one, mul_inv_rev]
    obtain ⟨i, b⟩ := l
    cases b <;> simp

end Eval

@[expose] def dWord : Fin 3 → M24Word :=
  ![[(9, true), (0, true), (2, true), (3, false), (5, true), (2, false)],
    [(6, true), (8, true), (2, true), (1, true), (3, true), (5, false), (4, true), (2, false)],
    [(9, true), (0, true), (1, true), (2, true), (5, false), (2, true)]]

@[expose] def thetaWord : Fin 3 → M24Word :=
  ![[(0, true), (3, true), (4, false), (5, true), (3, false)],
    [(6, true), (8, true), (9, true), (2, true), (1, true), (4, true), (2, false)],
    [(0, true), (1, true), (3, true), (4, false), (3, true)]]

@[expose] def uWord : M24Word := [(0, true), (2, true), (3, false), (2, true)]

@[expose] def nWord : M24Word :=
  [(0, true), (4, false), (3, true), (2, false), (0, true), (5, false)]

@[expose] def wWord : M24Word :=
  [(6, true), (9, true), (0, true), (4, false), (0, true), (2, false)]

end CFSG.CGT.M24R
