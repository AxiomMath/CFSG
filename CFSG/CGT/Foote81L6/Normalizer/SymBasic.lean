module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Equiv

theorem perm_eq_swap_of_sign {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ∀ σ : Perm (Fin n), σ * σ = 1 → Perm.sign σ = -1 → ∃ i j : Fin n, i ≠ j ∧ σ = swap i j := by
  rcases hn with rfl | rfl <;> decide +kernel

private theorem perm_exists_conj_swap_pair_four : ∀ a b c d : Fin 4, a ≠ b → c ≠ d →
    swap a b * swap c d = swap c d * swap a b → swap a b ≠ swap c d →
      ∃ ρ : Perm (Fin 4), ρ * swap a b * ρ⁻¹ = swap 0 1 ∧ ρ * swap c d * ρ⁻¹ = swap 2 3 := by
  decide +kernel

private theorem perm_exists_conj_swap_pair_five : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    swap a b * swap c d = swap c d * swap a b → swap a b ≠ swap c d →
      ∃ ρ : Perm (Fin 5), ρ * swap a b * ρ⁻¹ = swap 0 1 ∧ ρ * swap c d * ρ⁻¹ = swap 2 3 := by
  decide +kernel

theorem perm_exists_conj_swap_pair {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) :
    ∀ a b c d : Fin n, a ≠ b → c ≠ d → swap a b * swap c d = swap c d * swap a b →
      swap a b ≠ swap c d → ∃ ρ : Perm (Fin n), ρ * swap a b * ρ⁻¹ = swap 0 1 ∧
        ρ * swap c d * ρ⁻¹ = swap 2 3 := by
  rcases hn with rfl | rfl
  · exact perm_exists_conj_swap_pair_four
  · exact perm_exists_conj_swap_pair_five

private theorem perm_cycle_three_four :
    (swap (0 : Fin 4) 1 * swap 1 2) ^ 3 = 1 ∧ swap (0 : Fin 4) 1 * swap 1 2 ≠ 1 ∧
      swap (0 : Fin 4) 1 * (swap 0 1 * swap 1 2) * (swap 0 1)⁻¹ = (swap 0 1 * swap 1 2)⁻¹ := by
  decide +kernel

private theorem perm_cycle_three_five :
    (swap (0 : Fin 5) 1 * swap 1 2) ^ 3 = 1 ∧ swap (0 : Fin 5) 1 * swap 1 2 ≠ 1 ∧
      swap (0 : Fin 5) 1 * (swap 0 1 * swap 1 2) * (swap 0 1)⁻¹ = (swap 0 1 * swap 1 2)⁻¹ := by
  decide +kernel

theorem perm_cycle_three {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) :
    (swap (0 : Fin n) 1 * swap 1 2) ^ 3 = 1 ∧ swap (0 : Fin n) 1 * swap 1 2 ≠ 1 ∧
      swap (0 : Fin n) 1 * (swap 0 1 * swap 1 2) * (swap 0 1)⁻¹ = (swap 0 1 * swap 1 2)⁻¹ := by
  rcases hn with rfl | rfl
  · exact perm_cycle_three_four
  · exact perm_cycle_three_five

private theorem perm_mul_self_of_commute_four : ∀ σ : Perm (Fin 4),
    σ * swap 0 1 = swap 0 1 * σ → σ * swap 2 3 = swap 2 3 * σ → σ * σ = 1 := by
  decide +kernel

private theorem perm_mul_self_of_commute_five : ∀ σ : Perm (Fin 5),
    σ * swap 0 1 = swap 0 1 * σ → σ * swap 2 3 = swap 2 3 * σ → σ * σ = 1 := by
  decide +kernel

theorem perm_mul_self_of_commute {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) :
    ∀ σ : Perm (Fin n), σ * swap 0 1 = swap 0 1 * σ → σ * swap 2 3 = swap 2 3 * σ →
      σ * σ = 1 := by
  rcases hn with rfl | rfl
  · exact perm_mul_self_of_commute_four
  · exact perm_mul_self_of_commute_five

private theorem fin_zero_ne_one_four : (0 : Fin 4) ≠ 1 := by decide

private theorem fin_zero_ne_one_five : (0 : Fin 5) ≠ 1 := by decide

theorem fin_zero_ne_one_of {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) : (0 : Fin n) ≠ 1 := by
  rcases hn with rfl | rfl
  · exact fin_zero_ne_one_four
  · exact fin_zero_ne_one_five

private theorem perm_swap_pair_four :
    (2 : Fin 4) ≠ 3 ∧ swap (0 : Fin 4) 1 * swap 2 3 = swap 2 3 * swap 0 1 ∧
      swap (0 : Fin 4) 1 ≠ swap 2 3 := by
  decide

private theorem perm_swap_pair_five :
    (2 : Fin 5) ≠ 3 ∧ swap (0 : Fin 5) 1 * swap 2 3 = swap 2 3 * swap 0 1 ∧
      swap (0 : Fin 5) 1 ≠ swap 2 3 := by
  decide

theorem perm_swap_pair {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) :
    (2 : Fin n) ≠ 3 ∧ swap (0 : Fin n) 1 * swap 2 3 = swap 2 3 * swap 0 1 ∧
      swap (0 : Fin n) 1 ≠ swap 2 3 := by
  rcases hn with rfl | rfl
  · exact perm_swap_pair_four
  · exact perm_swap_pair_five

theorem perm_normalClosure_swap {α : Type*} [DecidableEq α] [Finite α] {a b : α} (hab : a ≠ b) :
    Subgroup.normalClosure ({swap a b} : Set (Perm α)) = ⊤ := by
  rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨x, y, hxy, rfl⟩
  exact Subgroup.conjugatesOfSet_subset_normalClosure
    (Group.mem_conjugatesOfSet_iff.mpr ⟨swap a b, rfl, Perm.isConj_swap hab hxy⟩)

theorem perm_four_klein :
    let z : Perm (Fin 4) := swap 0 1 * swap 2 3
    let u : Perm (Fin 4) := swap 0 2 * swap 1 3
    u ≠ z ∧ u * z = z * u ∧ u * u = 1 ∧ swap 1 2 * z * (swap 1 2)⁻¹ = u ∧
      u * swap 0 1 * u⁻¹ = swap 2 3 ∧
      ∀ m : Perm (Fin 4), (m * u * m⁻¹ = u ∨ m * u * m⁻¹ = z ∨ m * u * m⁻¹ = u * z) ∧
        (m * z * m⁻¹ = u ∨ m * z * m⁻¹ = z ∨ m * z * m⁻¹ = u * z) := by
  decide +kernel

theorem perm_five_cycle :
    let t : Perm (Fin 5) := swap 0 4 * swap 0 1
    t ^ 3 = 1 ∧ t ≠ 1 ∧ t * swap 2 3 = swap 2 3 * t ∧ swap 0 1 * t * (swap 0 1)⁻¹ = t⁻¹ ∧
      (∀ s : Perm (Fin 5), s * s = 1 → s * (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 * s →
        s * swap 0 1 * s⁻¹ = swap 2 3 → (t * s) ^ 5 = 1 ∧ t * s ≠ 1) ∧
      ∀ σ : Perm (Fin 5), σ * (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 * σ → σ 4 = 4 := by
  decide +kernel

theorem perm_five_card_fix :
    (Finset.univ.filter fun σ : Perm (Fin 5) => σ 4 = 4).card = 24 := by
  decide +kernel

end CFSG.CGT.Foote81L6.Normalizer
