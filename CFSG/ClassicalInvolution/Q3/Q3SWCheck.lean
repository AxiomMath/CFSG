module

public import CFSG.Monster.B.Co2.PermArr
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

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def cubeIdA (n : ℕ) (x : Array ℕ) : Bool := eqA n (compA n x (compA n x x)) (idA n)

@[expose] def witnessCheckA (n : ℕ) (g₁ g₂ z : Array ℕ) : Bool :=
  cubeIdA n g₁ && cubeIdA n g₂ && eqA n (compA n (compA n g₁ g₂) (compA n g₁ g₂)) (idA n) &&
    !eqA n (compA n g₁ g₂) (idA n) && !eqA n (compA n g₁ g₂) z

theorem witnessCheckA_sound {n : ℕ} {g₁ g₂ z : Array ℕ} {G₁ G₂ Z : Equiv.Perm (Fin n)}
    (h₁ : Rep n g₁ G₁) (h₂ : Rep n g₂ G₂) (hz : Rep n z Z)
    (h : witnessCheckA n g₁ g₂ z = true) :
    G₁ ^ 3 = 1 ∧ G₂ ^ 3 = 1 ∧ (G₁ * G₂) ^ 2 = 1 ∧ G₁ * G₂ ≠ 1 ∧ G₁ * G₂ ≠ Z := by
  simp only [witnessCheckA, cubeIdA, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hc₁, hc₂⟩, hsq⟩, hne1⟩, hnez⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_three]
    exact eq_of_eqA (rep_compA h₁ (rep_compA h₁ h₁)) rep_idA hc₁
  · rw [pow_three]
    exact eq_of_eqA (rep_compA h₂ (rep_compA h₂ h₂)) rep_idA hc₂
  · rw [sq]
    exact eq_of_eqA (rep_compA (rep_compA h₁ h₂) (rep_compA h₁ h₂)) rep_idA hsq
  · intro he
    have := (eqA_iff (rep_compA h₁ h₂) rep_idA).2 he
    rw [hne1] at this
    exact Bool.noConfusion this
  · intro he
    have := (eqA_iff (rep_compA h₁ h₂) hz).2 he
    rw [hnez] at this
    exact Bool.noConfusion this

end CFSG.ClassicalInvolution.Q3
