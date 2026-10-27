module

public import Certificates.Data.Kernel.Fi23Y322.Defs
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
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

namespace CFSG.KC.Fi23Y322

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KS.Raw.Orb

theorem tW_nil (G : Nat → Nat) (x : Nat) : tW G [] x = x := rfl

theorem tW_cons (G : Nat → Nat) (k : Nat) (u : List Nat) (x : Nat) :
    tW G (k :: u) x = tA G k (tW G u x) := by
  have e : tW G (k :: u) x = strictN (tW G u x) (tA G k) := rfl
  rw [e, strictN_eq]

theorem idK_spec {G : Nat → Nat} {u : List Nat} (h : idK G u = true) : ∀ b < 6, tW G u b = b :=
  fun b hb => Nat.eq_of_beq_eq_true (allN_iff.1 h b hb)

theorem fixL_spec {G : Nat → Nat} {w : List Nat} :
    ∀ ks : List Nat, fixL G w ks = true → ∀ k ∈ ks, k < 31671 ∧ wv G w k = k
  | [], _, k, hk => absurd hk List.not_mem_nil
  | a :: ks, h, k, hk => by
    have e : fixL G w (a :: ks) =
        bAnd(Nat.blt a (nat_lit 31671), bAnd(Nat.beq (wv G w a) a, fixL G w ks)) := rfl
    rw [e, bAnd_eq, bAnd_eq] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases List.mem_cons.1 hk with rfl | hk
    · exact ⟨by simpa [Nat.blt_eq] using h1, Nat.eq_of_beq_eq_true h2⟩
    · exact fixL_spec ks h3 k hk

theorem wordsK_spec {G : Nat → Nat} :
    ∀ W : List (List Nat), wordsK G W = true → ∀ u ∈ W, idK G u = true
  | [], _, u, hu => absurd hu List.not_mem_nil
  | a :: W, h, u, hu => by
    have e : wordsK G (a :: W) = bAnd(idK G a, wordsK G W) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h.1
    · exact wordsK_spec W h.2 u hu

theorem yK_spec {G : Nat → Nat} {w ks : List Nat} {W : List (List Nat)} {a b : Nat}
    (h : yK G w ks W a b = true) :
    (∀ k ∈ ks, k < 31671 ∧ wv G w k = k) ∧ (∀ u ∈ W, ∀ t < 6, tW G u t = t) ∧
      cmK G a b = false := by
  unfold yK at h
  rw [bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨fixL_spec ks h.1, fun u hu => idK_spec (wordsK_spec W h.2.1 u hu), h.2.2⟩

end CFSG.KC.Fi23Y322

end
