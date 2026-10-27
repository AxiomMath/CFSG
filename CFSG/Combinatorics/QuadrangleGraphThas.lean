module

public import CFSG.Combinatorics.QuadrangleGraphSpan
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Combinatorics.QuadrangleGraph

theorem mul_le_sq_of_counts {s t p N S₁ S₂ : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t)
    (hN : N + (t + 1) + (p + 1) * ((t + 1) * s + 1) =
      (s + 1) * (s * t + 1) + (p + 1) * (t + 1))
    (h₁ : S₁ + (t + 1) * ((p + 1) * s) = (t + 1) * ((t + 1) * s))
    (h₂ : S₂ + (t + 1) * (t * (p + 1) + (p + 1) * s) =
      (t + 1) * ((t + 1) * s + t * (t + 1)))
    (hCS : S₁ ^ 2 ≤ N * S₂) : p * t ≤ s ^ 2 := by
  zify at hN h₁ h₂ hCS ⊢
  have e₁ : (S₁ : ℤ) = ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * (s : ℤ) := by
    linear_combination h₁
  have e₂ : (S₂ : ℤ) = ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) *
      ((s : ℤ) + (t : ℤ)) := by
    linear_combination h₂
  have eN : (N : ℤ) = (s : ℤ) ^ 2 * (t : ℤ) - (p : ℤ) * (s : ℤ) * (t : ℤ) -
      (p : ℤ) * (s : ℤ) + (p : ℤ) * (t : ℤ) := by
    linear_combination hN
  have hspos : (0 : ℤ) < (s : ℤ) := by
    have : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
    linarith
  have htpos : (0 : ℤ) < (t : ℤ) := by
    have : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
    linarith
  have hK0 : (0 : ℤ) ≤ ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) := by
    have h0 : (0 : ℤ) ≤ (s : ℤ) * (((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ))) := by
      rw [mul_comm, ← e₁]
      exact Int.natCast_nonneg S₁
    exact (mul_nonneg_iff_of_pos_left hspos).mp h0
  have hKey : ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * (s : ℤ) ^ 2 ≤
      (N : ℤ) * ((s : ℤ) + (t : ℤ)) := by
    rcases lt_or_eq_of_le hK0 with hKpos | hKzero
    · have hmul : ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) *
          (((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * (s : ℤ) ^ 2) ≤
          ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) *
            ((N : ℤ) * ((s : ℤ) + (t : ℤ))) := by
        calc ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) *
              (((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * (s : ℤ) ^ 2)
            = (S₁ : ℤ) ^ 2 := by rw [e₁]; ring
          _ ≤ (N : ℤ) * (S₂ : ℤ) := hCS
          _ = ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) *
              ((N : ℤ) * ((s : ℤ) + (t : ℤ))) := by rw [e₂]; ring
      exact le_of_mul_le_mul_left hmul hKpos
    · rw [← hKzero]
      simpa using mul_nonneg (Int.natCast_nonneg N) (by linarith)
  have hId : (N : ℤ) * ((s : ℤ) + (t : ℤ)) -
      ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * (s : ℤ) ^ 2 =
      (t : ℤ) * ((s : ℤ) - 1) * ((s : ℤ) ^ 2 - (p : ℤ) * (t : ℤ)) := by
    rw [eN]
    ring
  have hpos : (0 : ℤ) < (t : ℤ) * ((s : ℤ) - 1) :=
    mul_pos htpos (by linarith)
  have hnonneg : (0 : ℤ) ≤ (t : ℤ) * ((s : ℤ) - 1) *
      ((s : ℤ) ^ 2 - (p : ℤ) * (t : ℤ)) := by
    rw [← hId]
    linarith
  have hlast : (0 : ℤ) ≤ (s : ℤ) ^ 2 - (p : ℤ) * (t : ℤ) :=
    (mul_nonneg_iff_of_pos_left hpos).mp hnonneg
  linarith

namespace IsQuadrangleOfOrder

variable {α : Type*} [Fintype α] {adj : α → α → Prop} {s t : ℕ}

theorem mul_le_sq (h : IsQuadrangleOfOrder adj s t) (hs : 2 ≤ s) (ht : 1 ≤ t) {x y : α}
    (hxy : ¬ adj x y) {p : ℕ} (hp : (span2 adj x y).card = p + 1) : p * t ≤ s ^ 2 := by
  classical
  obtain ⟨O, hO⟩ : ∃ O : Finset α, ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u :=
    ⟨Finset.univ.filter (fun w => ∀ u ∈ span2 adj x y, ¬ adj w u), fun w => by simp⟩
  let S₁ : ℕ := ∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card
  let S₂ : ℕ := ∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card ^ 2
  have hN := h.card_far ht hxy hp hO
  have h₁ : S₁ + (t + 1) * ((p + 1) * s) = (t + 1) * ((t + 1) * s) := by
    have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun w z => adj w z) (s := O) (t := perp2 adj x y)
    have hsum : S₁ = ∑ z ∈ perp2 adj x y, (O.filter fun w => adj w z).card := by
      rw [show S₁ = ∑ w ∈ O,
          ((perp2 adj x y).bipartiteAbove (fun w z => adj w z) w).card from rfl, hdouble]
      rfl
    have hterm : ∀ z ∈ perp2 adj x y,
        (O.filter fun w => adj w z).card + (p + 1) * s = (t + 1) * s :=
      fun z hz => h.card_filter_adj_of_mem_perp2 ht hxy hp hO hz
    have hconst : (t + 1) * ((p + 1) * s) =
        ∑ _z ∈ perp2 adj x y, (p + 1) * s := by
      rw [Finset.sum_const_nat (m := (p + 1) * s) (f := fun _ => (p + 1) * s)
        (fun _ _ => rfl), h.card_perp hxy]
    rw [hsum, hconst, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm]
    rw [Finset.sum_const_nat (m := (t + 1) * s) (f := fun _ => (t + 1) * s)
      (fun _ _ => rfl), h.card_perp hxy]
  have h₂ : S₂ + (t + 1) * (t * (p + 1) + (p + 1) * s) =
      (t + 1) * ((t + 1) * s + t * (t + 1)) := by
    have hS₂ : S₂ = ∑ z ∈ perp2 adj x y, ∑ z' ∈ perp2 adj x y,
        (O.filter fun w => adj w z ∧ adj w z').card :=
      sum_sq_card_filter_adj O (perp2 adj x y)
    have hterm : ∀ z ∈ perp2 adj x y,
        (∑ z' ∈ perp2 adj x y, (O.filter fun w => adj w z ∧ adj w z').card) +
          (t * (p + 1) + (p + 1) * s) = (t + 1) * s + t * (t + 1) := by
      intro z hz
      simpa only [Nat.add_assoc] using h.sum_card_filter_adj_adj_row ht hxy hp hO hz
    have hconst : (t + 1) * (t * (p + 1) + (p + 1) * s) =
        ∑ _z ∈ perp2 adj x y, (t * (p + 1) + (p + 1) * s) := by
      rw [Finset.sum_const_nat (m := t * (p + 1) + (p + 1) * s)
        (f := fun _ => t * (p + 1) + (p + 1) * s) (fun _ _ => rfl), h.card_perp hxy]
    rw [hS₂, hconst, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm]
    rw [Finset.sum_const_nat (m := (t + 1) * s + t * (t + 1))
      (f := fun _ => (t + 1) * s + t * (t + 1)) (fun _ _ => rfl), h.card_perp hxy]
  have hCS : S₁ ^ 2 ≤ O.card * S₂ := by
    change (∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card) ^ 2 ≤
      O.card * ∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card ^ 2
    have h := sq_sum_le_card_mul_sum_sq (s := O)
      (f := fun w => ((perp2 adj x y).filter fun z => adj w z).card)
    simpa only [Nat.cast_id] using h
  exact mul_le_sq_of_counts hs ht hN h₁ h₂ hCS

end IsQuadrangleOfOrder

end CFSG.Combinatorics.QuadrangleGraph
