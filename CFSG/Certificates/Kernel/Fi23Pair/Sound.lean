module

public import Certificates.Data.Kernel.Fi23Pair.Defs
public import CFSG.Certificates.Kernel.Fi23Q.WordSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
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

public section

namespace CFSG.KS.Fi23Pair

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Fi23R CFSG.KC.Fi23Pair CFSG.KS.Raw.Orb

theorem not_eqH {G : Nat → Nat} {y : List Nat} (h : Bool.not (eqH G y []) = true) :
    ¬ (∀ b < 6, wv G y b = wv G [] b) := by
  intro hy
  have : eqH G y [] = true := by
    unfold eqH
    refine allN_iff.2 fun b hb => ?_
    rw [hy b hb]
    exact Nat.beq_refl _
  rw [this] at h
  exact Bool.false_ne_true h

theorem ordK_spec {G : Nat → Nat} {e : Nat} {y t : List Nat} (h : ordK G e y t = true) :
    (∀ b < 6, wv G (powW e y) b = wv G [] b) ∧ ¬ (∀ b < 6, wv G y b = wv G [] b) ∧
      ∀ b < 6, wv G (y ++ t) b = wv G (t ++ y) b := by
  unfold ordK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨eqH_spec h1, not_eqH h2, eqH_spec h3⟩

theorem stK_spec {G : Nat → Nat} {s t : List Nat} {p : Nat} (h : stK G s t p = true) :
    (∀ b < 6, wv G (powW 3 s) b = wv G [] b) ∧ ¬ (∀ b < 6, wv G s b = wv G [] b) ∧
      wv G s p = p ∧ wv G t p = p := by
  unfold stK at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨eqH_spec h1, not_eqH h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

end CFSG.KS.Fi23Pair

end
