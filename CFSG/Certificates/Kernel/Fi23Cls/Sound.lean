module

public import Certificates.Data.Kernel.Fi23Cls.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.Fi23Cls

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Five CFSG.KS.Raw.Orb

theorem cntL_cons (q : Nat → Bool) (r : Nat) (L : List Nat) :
    cntL q (r :: L) = if q r = true then cntL q L + 1 else cntL q L := by
  have e : cntL q (r :: L) = strictN (cntL q L) fun n => nIf(q r, Nat.succ n, n) := rfl
  rw [e, strictN_eq, nIf_eq]

theorem cntL_eq (q : Nat → Bool) : ∀ L : List Nat, cntL q L = L.countP q
  | [] => rfl
  | r :: L => by
    rw [cntL_cons, List.countP_cons, cntL_eq q L]
    split_ifs <;> simp_all

theorem stepD_spec {G : Nat → Nat} {w : List Nat} {p r s : Nat} (h : stepD G w p r s = true) :
    r = p ∨ cmK G p r = false ∨
      (s < 31671 ∧ wv G w s = s ∧ cmK G p s = false ∧ cmK G s r = false) := by
  unfold stepD at h
  rw [bIf_eq, bIf_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  by_cases h1 : Nat.beq r p = true
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · rw [if_neg h1] at h
    by_cases h2 : cmK G p r = true
    · rw [if_pos h2] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨h3, h4, h5, h6⟩ := h
      exact Or.inr (Or.inr ⟨by simpa [Nat.blt_eq] using h3, Nat.eq_of_beq_eq_true h4, h5, h6⟩)
    · exact Or.inr (Or.inl (by simpa using h2))

theorem diamK_cons (G : Nat → Nat) (w : List Nat) (p r : Nat) (L : List Nat) (s : Nat)
    (S : List Nat) : diamK G w p (r :: L) (s :: S) = (stepD G w p r s && diamK G w p L S) := by
  have e : diamK G w p (r :: L) (s :: S) =
      Bool.rec (motive := fun _ => Bool) false (diamK G w p L S) (stepD G w p r s) := rfl
  rw [e, bAnd_eq]

theorem diamK_spec {G : Nat → Nat} {w : List Nat} {p : Nat} :
    ∀ (L S : List Nat), diamK G w p L S = true → ∀ r ∈ L, r = p ∨ cmK G p r = false ∨
      ∃ s, s < 31671 ∧ wv G w s = s ∧ cmK G p s = false ∧ cmK G s r = false
  | [], _, _, r, hr => absurd hr List.not_mem_nil
  | _ :: _, [], h, _, _ => absurd h (by intro h'; cases h')
  | a :: L, s :: S, h, r, hr => by
    rw [diamK_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hr with rfl | hr
    · rcases stepD_spec h.1 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨s, h1⟩)
    · exact diamK_spec L S h.2 r hr

theorem clsK_spec {G : Nat → Nat} {w : List Nat} {p N V : Nat} {L S : List Nat}
    (h : clsK G w p N V L S = true) :
    (∀ t < 6, wv G w (wv G w (wv G w t)) = t) ∧ p < 31671 ∧ wv G w p = p ∧ L.length = N ∧
      L.countP (valF G p) = V ∧
      ∀ r ∈ L, r = p ∨ cmK G p r = false ∨
        ∃ s, s < 31671 ∧ wv G w s = s ∧ cmK G p s = false ∧ cmK G s r = false := by
  unfold clsK at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun t ht => ?_, by simpa [Nat.blt_eq] using h2, Nat.eq_of_beq_eq_true h3, ?_, ?_,
    diamK_spec L S h6⟩
  · unfold ord3K at h1
    exact Nat.eq_of_beq_eq_true (allN_iff.1 h1 t ht)
  · rw [← Nat.eq_of_beq_eq_true h4, cntL_eq, List.countP_true]
  · rw [← Nat.eq_of_beq_eq_true h5, cntL_eq]

theorem valF_iff {G : Nat → Nat} {p r : Nat} : valF G p r = true ↔ r ≠ p ∧ cmK G p r = true := by
  unfold valF
  rw [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, h2⟩
    rw [h, Nat.beq_refl] at h1
    cases h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    cases e : Nat.beq r p
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h1

end CFSG.KC.Fi23Cls

end
