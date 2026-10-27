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

namespace CFSG.Certificates.Kernel.CatFacts

theorem fix_card_mod_five {n : Nat} {x s : Equiv.Perm (Fin n)} (hx5 : x ^ 5 = 1)
    (hfree : ∀ j, x j ≠ j) (hc : x * s = s * x) :
    (Finset.univ.filter fun j => s j = j).card % 5 = 0 := by
  have hxs : ∀ j, s j = j → s (x j) = x j := by
    intro j hj
    have h := congrArg (fun g : Equiv.Perm (Fin n) => g j) hc
    simp only [Equiv.Perm.mul_apply] at h
    rw [← h, hj]
  let f : Function.End {j // s j = j} := fun a => ⟨x a.1, hxs a.1 a.2⟩
  have hpow : ∀ (k : Nat) (a : {j // s j = j}), ((f ^ k) a).1 = (x ^ k) a.1 := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply]
      exact ih (f a)
  have hf : f ^ 5 ^ 1 = 1 := by
    funext a
    apply Subtype.ext
    rw [pow_one, hpow, hx5]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) (hp := ⟨by norm_num⟩) hf
  have h0 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun a => hfree a.1.1 ?_⟩
    have := a.2
    exact congrArg Subtype.val this
  rw [h0, Fintype.card_subtype] at hmod
  exact hmod

end CFSG.Certificates.Kernel.CatFacts

end
