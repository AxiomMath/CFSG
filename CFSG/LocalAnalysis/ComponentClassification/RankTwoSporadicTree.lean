module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open

variable {W : Type*} [Group W] [Finite W]

theorem forall_of_tree {S : Subgroup W} (Wit Mono : Subgroup W → Prop)
    (hMono : ∀ E₀ E : Subgroup W, Mono E₀ → E₀ ≤ E → E ≤ S → IsElemAbelian 2 E →
      4 ≤ Nat.card E → Wit E)
    (node : ℕ → Subgroup W) (N : ℕ)
    (hroot : ∀ a ∈ S, a ^ 2 = 1 → a ≠ 1 → ∃ i < N, node i = zpowers a)
    (hchild : ∀ i < N, Mono (node i) ∨ ∀ u ∈ S, u ^ 2 = 1 → u ∉ node i →
      (∀ x ∈ node i, x * u = u * x) → ∃ j < N, node j = node i ⊔ zpowers u)
    (hwit : ∀ i < N, 4 ≤ Nat.card (node i) → Mono (node i) ∨ Wit (node i))
    {E : Subgroup W} (hES : E ≤ S) (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) : Wit E := by
  have key : ∀ k : ℕ, ∀ i < N, node i ≤ E → Nat.card E ≤ Nat.card (node i) + k → Wit E := by
    intro k
    induction k with
    | zero =>
      intro i hi hiE hcard
      have heq : node i = E := eq_of_le_of_card_ge hiE (by omega)
      rcases hwit i hi (heq ▸ hE4) with hm | hw
      · exact hMono _ _ hm hiE hES hE hE4
      · exact heq ▸ hw
    | succ k ih =>
      intro i hi hiE hcard
      rcases hchild i hi with hm | hch
      · exact hMono _ _ hm hiE hES hE hE4
      by_cases heq : node i = E
      · rcases hwit i hi (heq ▸ hE4) with hm | hw
        · exact hMono _ _ hm hiE hES hE hE4
        · exact heq ▸ hw
      obtain ⟨u, huE, hui⟩ : ∃ u ∈ E, u ∉ node i := by
        by_contra hcon
        push Not at hcon
        exact heq (le_antisymm hiE hcon)
      have hcomm : ∀ x ∈ node i, x * u = u * x := fun x hx =>
        congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hiE hx⟩ ⟨u, huE⟩)
      obtain ⟨j, hj, hjeq⟩ := hch u (hES huE) (hE.2 u huE) hui hcomm
      have hjE : node j ≤ E := hjeq ▸ sup_le hiE (zpowers_le.mpr huE)
      have hlt : Nat.card (node i) < Nat.card (node j) := by
        have hle : node i ≤ node j := hjeq ▸ le_sup_left
        have hne : node i ≠ node j := fun h =>
          hui (h ▸ (hjeq ▸ mem_sup_right (mem_zpowers u) : u ∈ node j))
        exact card_lt_of_lt (lt_of_le_of_ne hle hne)
      exact ih j hj hjE (by omega)
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hcon x hx)
    rw [hbot, card_bot] at hE4
    omega
  obtain ⟨i, hi, hieq⟩ := hroot a (hES haE) (hE.2 a haE) ha1
  exact key (Nat.card E) i hi (hieq ▸ zpowers_le.mpr haE) (by omega)

end CFSG.ComponentClassification.RankTwoSporadic
