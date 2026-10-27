module

public import CFSG.Combinatorics.QuadrangleGraphSpan
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Combinatorics.QuadrangleGraph

namespace IsQuadrangleOfOrder

variable {α : Type*} [Fintype α] {adj : α → α → Prop} {s t : ℕ}

private theorem card_filter_adj_eq_of_row {O : Finset α} {b : α → ℕ} {S₁ : ℕ} {w : α}
    {p : ℕ} (hbw : (O.card : ℤ) * (b w) = (S₁ : ℤ))
    (eN : (O.card : ℤ) = (s : ℤ) * ((s : ℤ) - (p : ℤ)) * ((t : ℤ) + 1))
    (e₁ : (S₁ : ℤ) = ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * (s : ℤ))
    (hpt : p * t = s ^ 2) (hspos : (0 : ℤ) < (s : ℤ))
    (hsubpos : (0 : ℤ) < (s : ℤ) - (p : ℤ)) :
    p * b w = s + p := by
    have hptZ : (p : ℤ) * (t : ℤ) = (s : ℤ) ^ 2 := by exact_mod_cast hpt
    have hfac : ((s : ℤ) - (p : ℤ)) * (b w) = (t : ℤ) - (p : ℤ) := by
      have hprod : ((s : ℤ) * ((t : ℤ) + 1)) *
          (((s : ℤ) - (p : ℤ)) * (b w) - ((t : ℤ) - (p : ℤ))) = 0 := by
        linear_combination hbw - (b w) * eN + e₁
      have hprod' : ((s : ℤ) * ((t : ℤ) + 1)) *
          (((s : ℤ) - (p : ℤ)) * (b w) - ((t : ℤ) - (p : ℤ))) =
          ((s : ℤ) * ((t : ℤ) + 1)) * 0 := by
        rw [mul_zero]
        exact hprod
      exact sub_eq_zero.mp
        (mul_left_cancel₀ (ne_of_gt (mul_pos hspos (by positivity))) hprod')
    have hpbZ : (p : ℤ) * (b w) = (s : ℤ) + (p : ℤ) := by
      have hkey : ((s : ℤ) - (p : ℤ)) * ((p : ℤ) * (b w)) =
          ((s : ℤ) - (p : ℤ)) * ((s : ℤ) + (p : ℤ)) := by
        calc ((s : ℤ) - (p : ℤ)) * ((p : ℤ) * (b w))
            = (p : ℤ) * (((s : ℤ) - (p : ℤ)) * (b w)) := by ring
          _ = (p : ℤ) * ((t : ℤ) - (p : ℤ)) := by rw [hfac]
          _ = ((s : ℤ) - (p : ℤ)) * ((s : ℤ) + (p : ℤ)) := by linear_combination hptZ
      exact mul_left_cancel₀ (ne_of_gt hsubpos) hkey
    exact_mod_cast hpbZ

private theorem card_far_and_row_counts [DecidableRel adj] (h : IsQuadrangleOfOrder adj s t)
    (ht : 1 ≤ t) {x y : α} (hxy : ¬ adj x y) {p : ℕ}
    (hp : (span2 adj x y).card = p + 1) {O : Finset α}
    (hO : ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u) :
    O.card + (t + 1) + (p + 1) * ((t + 1) * s + 1) =
        (s + 1) * (s * t + 1) + (p + 1) * (t + 1) ∧
      (∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card) +
          (t + 1) * ((p + 1) * s) = (t + 1) * ((t + 1) * s) ∧
      (∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card ^ 2) +
          (t + 1) * (t * (p + 1) + (p + 1) * s) =
        (t + 1) * ((t + 1) * s + t * (t + 1)) := by
  classical
  refine ⟨h.card_far ht hxy hp hO, ?_, ?_⟩
  · have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun w z => adj w z) (s := O) (t := perp2 adj x y)
    have hsum : (∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card) =
        ∑ z ∈ perp2 adj x y, (O.filter fun w => adj w z).card := by
      rw [show (∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card) =
          ∑ w ∈ O, ((perp2 adj x y).bipartiteAbove (fun w z => adj w z) w).card from rfl,
        hdouble]
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
  · have hS₂ : (∑ w ∈ O, ((perp2 adj x y).filter fun z => adj w z).card ^ 2) =
        ∑ z ∈ perp2 adj x y, ∑ z' ∈ perp2 adj x y,
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

private theorem mul_card_filter_adj_of_counts [DecidableRel adj] (h : IsQuadrangleOfOrder adj s t)
    (ht : 1 ≤ t) {x y : α} (hxy : ¬ adj x y) {p : ℕ}
    (hp : (span2 adj x y).card = p + 1) (hpt : p * t = s ^ 2) {O : Finset α}
    (hO : ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u) {w : α} (hw : w ∈ O) :
    p * ((perp2 adj x y).filter (adj w)).card = s + p := by
  classical
  let b : α → ℕ := fun z => ((perp2 adj x y).filter fun z' => adj z z').card
  let S₁ : ℕ := ∑ z ∈ O, b z
  let S₂ : ℕ := ∑ z ∈ O, b z ^ 2
  obtain ⟨hN, h₁, h₂⟩ := card_far_and_row_counts h ht hxy hp hO
  have h₁' : S₁ + (t + 1) * ((p + 1) * s) = (t + 1) * ((t + 1) * s) := by
    simpa [S₁, b] using h₁
  have h₂' : S₂ + (t + 1) * (t * (p + 1) + (p + 1) * s) =
      (t + 1) * ((t + 1) * s + t * (t + 1)) := by
    simpa [S₂, b] using h₂
  have hNpos : (0 : ℤ) < (O.card : ℤ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨w, hw⟩
  zify at hN h₁' h₂'
  have hptZ : (p : ℤ) * (t : ℤ) = (s : ℤ) ^ 2 := by exact_mod_cast hpt
  have e₁ : (S₁ : ℤ) = ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * (s : ℤ) := by
    linear_combination h₁'
  have e₂ : (S₂ : ℤ) = ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * ((s : ℤ) + (t : ℤ)) := by
    linear_combination h₂'
  have eN : (O.card : ℤ) = (s : ℤ) * ((s : ℤ) - (p : ℤ)) * ((t : ℤ) + 1) := by
    linear_combination hN + hptZ
  have hEq : (O.card : ℤ) * (S₂ : ℤ) = (S₁ : ℤ) ^ 2 := by
    linear_combination (O.card : ℤ) * e₂ +
      (((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * ((s : ℤ) + (t : ℤ))) * eN -
      ((S₁ : ℤ) + ((t : ℤ) + 1) * ((t : ℤ) - (p : ℤ)) * (s : ℤ)) * e₁ -
      (((t : ℤ) + 1) ^ 2 * ((t : ℤ) - (p : ℤ)) * (s : ℤ)) * hptZ
  have hspos : (0 : ℤ) < (s : ℤ) := by
    by_contra hs
    have hs0 : (s : ℤ) = 0 := le_antisymm (by linarith) (by exact_mod_cast Nat.zero_le s)
    rw [hs0] at eN
    simpa [eN] using hNpos
  have hsubpos : (0 : ℤ) < (s : ℤ) - (p : ℤ) := by
    have ht1 : (0 : ℤ) < (t : ℤ) + 1 := by positivity
    rw [eN, mul_assoc] at hNpos
    exact Int.pos_of_mul_pos_left
      (pos_of_mul_pos_right hNpos (le_of_lt hspos)) ht1
  have hsum_id : ∑ z ∈ O, ((O.card : ℤ) * (b z) - (S₁ : ℤ)) ^ 2 =
      (O.card : ℤ) * ((O.card : ℤ) * (S₂ : ℤ) - (S₁ : ℤ) ^ 2) := by
    have hb1 : ∑ z ∈ O, (b z : ℤ) = (S₁ : ℤ) := by simp [S₁]
    have hb2 : ∑ z ∈ O, (b z : ℤ) ^ 2 = (S₂ : ℤ) := by simp [S₂]
    have hterm : ∀ z ∈ O, ((O.card : ℤ) * (b z) - (S₁ : ℤ)) ^ 2 =
        (O.card : ℤ) ^ 2 * (b z : ℤ) ^ 2 -
          2 * (O.card : ℤ) * (S₁ : ℤ) * (b z : ℤ) + (S₁ : ℤ) ^ 2 :=
      fun z _ => by ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, hb1, hb2]
    simp only [nsmul_eq_mul]
    ring
  have hsumZero : ∑ z ∈ O, ((O.card : ℤ) * (b z) - (S₁ : ℤ)) ^ 2 = 0 := by
    rw [hsum_id, hEq, sub_self, mul_zero]
  have hbw : (O.card : ℤ) * (b w) = (S₁ : ℤ) := by
    have hzero : ((O.card : ℤ) * (b w) - (S₁ : ℤ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := O)
        (f := fun z => ((O.card : ℤ) * (b z) - (S₁ : ℤ)) ^ 2)
        (fun z _ => sq_nonneg _)).mp hsumZero w hw
    exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp hzero)
  simpa [b] using card_filter_adj_eq_of_row hbw eN e₁ hpt hspos hsubpos

theorem mul_card_filter_adj_eq [DecidableRel adj] (h : IsQuadrangleOfOrder adj s t)
    (ht : 1 ≤ t) {x y : α} (hxy : ¬ adj x y) {p : ℕ} (hp : (span2 adj x y).card = p + 1)
    (hpt : p * t = s ^ 2) {w : α} (hw : ∀ u ∈ span2 adj x y, ¬ adj w u) :
    p * ((perp2 adj x y).filter (adj w)).card = s + p := by
  classical
  obtain ⟨O, hO⟩ : ∃ O : Finset α, ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u :=
    ⟨Finset.univ.filter (fun w => ∀ u ∈ span2 adj x y, ¬ adj w u), fun w => by simp⟩
  exact mul_card_filter_adj_of_counts h ht hxy hp hpt hO (by rw [hO w]; exact hw)

end IsQuadrangleOfOrder

end CFSG.Combinatorics.QuadrangleGraph
