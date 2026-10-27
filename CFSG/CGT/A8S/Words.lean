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

namespace CFSG.CGT.A8S

abbrev A8Word : Type := List (Fin 6 × Bool)

@[expose] def evalA8 {H : Type*} [Group H] (e : Fin 6 → H) (w : A8Word) : H :=
  FreeGroup.lift e (FreeGroup.mk w)

@[expose] def invA8 (w : A8Word) : A8Word := w.reverse.map fun p => (p.1, !p.2)

@[expose] def liftW5 (w : List (Fin 5 × Bool)) : A8Word :=
  w.map fun p => (Fin.castSucc p.1, p.2)

section Eval

variable {H : Type*} [Group H] (e : Fin 6 → H)

@[simp] theorem evalA8_nil : evalA8 e [] = 1 := map_one _

theorem evalA8_cons (l : Fin 6 × Bool) (w : A8Word) :
    evalA8 e (l :: w) = (if l.2 then e l.1 else (e l.1)⁻¹) * evalA8 e w := by
  unfold evalA8
  rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
  obtain ⟨i, b⟩ := l
  cases b
  · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
      FreeGroup.lift_apply_of]
    rfl
  · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
    rfl

@[simp] theorem evalA8_cons_true (i : Fin 6) (w : A8Word) :
    evalA8 e ((i, true) :: w) = e i * evalA8 e w := evalA8_cons e _ w

@[simp] theorem evalA8_cons_false (i : Fin 6) (w : A8Word) :
    evalA8 e ((i, false) :: w) = (e i)⁻¹ * evalA8 e w := evalA8_cons e _ w

theorem evalA8_append (w w' : A8Word) : evalA8 e (w ++ w') = evalA8 e w * evalA8 e w' := by
  unfold evalA8
  rw [← FreeGroup.mul_mk, map_mul]

theorem evalA8_invA8 (w : A8Word) : evalA8 e (invA8 w) = (evalA8 e w)⁻¹ := by
  induction w with
  | nil => simp [invA8]
  | cons l w ih =>
    have h : invA8 (l :: w) = invA8 w ++ [(l.1, !l.2)] := by simp [invA8]
    rw [h, evalA8_append, ih, evalA8_cons, evalA8_cons, evalA8_nil, mul_one, mul_inv_rev]
    obtain ⟨i, b⟩ := l
    cases b <;> simp

theorem evalA8_liftW5 (w : List (Fin 5 × Bool)) :
    evalA8 e (liftW5 w) = FreeGroup.lift (fun i : Fin 5 => e (Fin.castSucc i))
      (FreeGroup.mk w) := by
  rw [evalA8, FreeGroup.lift_mk, FreeGroup.lift_mk, liftW5, List.map_map]
  rfl

end Eval

end CFSG.CGT.A8S
