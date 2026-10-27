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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

@[expose] def commIter (M : Subgroup X) : ℕ → Subgroup X
  | 0 => M
  | n + 1 => ⁅commIter M n, (⊤ : Subgroup X)⁆

theorem commIter_succ' (M : Subgroup X) (n : ℕ) :
    commIter M (n + 1) = commIter ⁅M, (⊤ : Subgroup X)⁆ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [commIter, ih]; rfl

@[expose] def ChiefTrivial (O : Subgroup X) : Prop :=
  ∀ B N : Subgroup X, B.Normal → N.Normal → B ≤ N → N ≤ O →
    (∀ K : Subgroup X, K.Normal → B ≤ K → K ≤ N → K = B ∨ K = N) →
    ⁅N, (⊤ : Subgroup X)⁆ ≤ B

theorem exists_commIter_le [Finite X] {O : Subgroup X} (h : ChiefTrivial O) :
    ∀ (d : ℕ) (B M : Subgroup X), B.Normal → M.Normal → B ≤ M → M ≤ O →
      Nat.card M - Nat.card B ≤ d → ∃ n, commIter M n ≤ B := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro B M hB hM hBM hMO hd
    by_cases hBeq : B = M
    · exact ⟨0, hBeq ▸ le_rfl⟩
    have hlt : B < M := lt_of_le_of_ne hBM hBeq
    have := hB
    have := hM
    let S : Set (Subgroup X) := {K | K.Normal ∧ B < K ∧ K ≤ M}
    have hSne : S.Nonempty := ⟨M, hM, hlt, le_rfl⟩
    obtain ⟨N, hNS, hNmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min S hSne
    obtain ⟨hNn, hBN, hNM⟩ := hNS
    have := hNn
    have hchief : ∀ K : Subgroup X, K.Normal → B ≤ K → K ≤ N → K = B ∨ K = N := by
      intro K hK hBK hKN
      by_cases hKB : K = B
      · exact Or.inl hKB
      · right
        have hBK' : B < K := lt_of_le_of_ne hBK (Ne.symm hKB)
        by_contra hKN'
        exact hNmin K ⟨hK, hBK', hKN.trans hNM⟩ (lt_of_le_of_ne hKN hKN')
    have h1 : ⁅N, (⊤ : Subgroup X)⁆ ≤ B := h B N hB hNn hBN.le (hNM.trans hMO) hchief
    have hcard : Nat.card B < Nat.card N := by
      have := Subgroup.card_le_of_le hBN.le
      have hne : Nat.card B ≠ Nat.card N := fun heq =>
        hBN.ne (Subgroup.eq_of_le_of_card_ge hBN.le (by omega))
      omega
    have hcardNM : Nat.card N ≤ Nat.card M := Subgroup.card_le_of_le hNM
    obtain ⟨n, hn⟩ := ih (Nat.card M - Nat.card N) (by omega) N M hNn hM hNM hMO le_rfl
    exact ⟨n + 1, (Subgroup.commutator_mono hn le_rfl).trans h1⟩

theorem commutator_eq_bot_of_commIter (hX : commutator X = ⊤) :
    ∀ (n : ℕ) (M : Subgroup X), M.Normal → commIter M n = ⊥ → ⁅M, (⊤ : Subgroup X)⁆ = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro M _ hM
    rw [commIter] at hM
    rw [hM]
    exact Subgroup.commutator_bot_left _
  | succ n ih =>
    intro M hM h
    rw [commIter_succ'] at h
    have h1 : ⁅⁅M, (⊤ : Subgroup X)⁆, (⊤ : Subgroup X)⁆ = ⊥ :=
      ih ⁅M, (⊤ : Subgroup X)⁆ (Subgroup.commutator_normal _ _) h
    have h2 : ⁅⁅(⊤ : Subgroup X), M⁆, (⊤ : Subgroup X)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (⊤ : Subgroup X) M]
      exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := (⊤ : Subgroup X))
      (H₂ := (⊤ : Subgroup X)) (H₃ := M) h2 h1
    have h4 : ⁅(commutator X), M⁆ = ⊥ := h3
    rw [hX] at h4
    rw [Subgroup.commutator_comm]
    exact h4

theorem le_center_of_chiefTrivial [Finite X] (hX : commutator X = ⊤) {O : Subgroup X}
    [O.Normal] (h : ChiefTrivial O) : O ≤ center X := by
  obtain ⟨n, hn⟩ := exists_commIter_le h _ ⊥ O inferInstance inferInstance bot_le le_rfl le_rfl
  have hcomm : ⁅O, (⊤ : Subgroup X)⁆ = ⊥ :=
    commutator_eq_bot_of_commIter hX n O inferInstance (le_bot_iff.1 hn)
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro g
  have : ⁅o, g⁆ = 1 := by
    have hm : ⁅o, g⁆ ∈ ⁅O, (⊤ : Subgroup X)⁆ := Subgroup.commutator_mem_commutator ho (mem_top g)
    rw [hcomm] at hm
    exact Subgroup.mem_bot.1 hm
  exact (commutatorElement_eq_one_iff_commute.1 this).eq.symm

end CFSG.EvenSporadicStandard.M24Std
