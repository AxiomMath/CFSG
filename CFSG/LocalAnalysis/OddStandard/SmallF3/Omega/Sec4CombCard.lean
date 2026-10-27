module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private instance instDecidableIsEvenVec {n : ℕ} (v : Fin n → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private lemma card_weightSet (W : Set ℕ) [Decidable (2 ∈ W)] [Decidable (4 ∈ W)]
    [Decidable (6 ∈ W)] (hW : ∀ k ∈ W, k = 2 ∨ k = 4 ∨ k = 6) :
    Nat.card {v : Fin 7 → ZMod 2 | IsEvenVec v ∧ vecWeight v ∈ W} =
      (if 2 ∈ W then 21 else 0) + (if 4 ∈ W then 35 else 0) + (if 6 ∈ W then 7 else 0) := by
  have hchar : ∀ v : Fin 7 → ZMod 2, vecWeight v ∈ W ↔
      (vecWeight v = 2 ∧ 2 ∈ W) ∨ (vecWeight v = 4 ∧ 4 ∈ W) ∨
        (vecWeight v = 6 ∧ 6 ∈ W) := by
    intro v
    constructor
    · intro hv
      rcases hW _ hv with h | h | h
      · exact Or.inl ⟨h, h ▸ hv⟩
      · exact Or.inr (Or.inl ⟨h, h ▸ hv⟩)
      · exact Or.inr (Or.inr ⟨h, h ▸ hv⟩)
    · rintro (⟨h, h2⟩ | ⟨h, h4⟩ | ⟨h, h6⟩)
      · rw [h]; exact h2
      · rw [h]; exact h4
      · rw [h]; exact h6
  have hset : {v : Fin 7 → ZMod 2 | IsEvenVec v ∧ vecWeight v ∈ W} =
      {v : Fin 7 → ZMod 2 | IsEvenVec v ∧ ((vecWeight v = 2 ∧ 2 ∈ W) ∨
        (vecWeight v = 4 ∧ 4 ∈ W) ∨ (vecWeight v = 6 ∧ 6 ∈ W))} := by
    ext v
    simp only [Set.mem_setOf_eq]
    rw [hchar v]
  rw [hset]
  by_cases h2 : 2 ∈ W <;> by_cases h4 : 4 ∈ W <;> by_cases h6 : 6 ∈ W <;>
    (simp only [h2, h4, h6, and_true, and_false, true_and, false_and, or_true, or_false, true_or,
      false_or, if_true, if_false] <;>
      rw [Nat.card_eq_fintype_card] <;> decide +kernel)

theorem card_weightClosed_of_four {S : Set (Fin 7 → ZMod 2)}
    (hS : ∀ v ∈ S, IsEvenVec v ∧ v ≠ 0)
    (hcl : ∀ v ∈ S, ∀ w : Fin 7 → ZMod 2, IsEvenVec w → vecWeight w = vecWeight v → w ∈ S)
    (h4 : ∃ v ∈ S, vecWeight v = 4) :
    Nat.card S = 35 ∨ Nat.card S = 42 ∨ Nat.card S = 56 ∨ Nat.card S = 63 := by
  classical
  set W : Set ℕ := {k | ∃ v ∈ S, vecWeight v = k} with hWdef
  have hmem : ∀ k, k ∈ W ↔ ∃ v, v ∈ S ∧ vecWeight v = k := by
    intro k
    rw [hWdef]
    rfl
  have hS_eq : S = {v | IsEvenVec v ∧ vecWeight v ∈ W} := by
    ext v
    constructor
    · intro hv
      exact ⟨(hS v hv).1, (hmem (vecWeight v)).mpr ⟨v, hv, rfl⟩⟩
    · rintro ⟨hv, hmem_v⟩
      obtain ⟨u, hu, hwu⟩ := (hmem (vecWeight v)).mp hmem_v
      exact hcl u hu v hv hwu.symm
  have hW : ∀ k ∈ W, k = 2 ∨ k = 4 ∨ k = 6 := by
    intro k hk
    obtain ⟨v, hv, hwv⟩ := (hmem k).mp hk
    have hev : IsEvenVec v := (hS v hv).1
    have hv0 : v ≠ 0 := (hS v hv).2
    rcases vecWeight_cases_of_isEvenVec hev with h0 | h2 | h4' | h6
    · exact absurd (eq_zero_of_vecWeight_eq_zero h0) hv0
    · exact Or.inl (hwv ▸ h2)
    · exact Or.inr (Or.inl (hwv ▸ h4'))
    · exact Or.inr (Or.inr (hwv ▸ h6))
  have h4W : 4 ∈ W := (hmem 4).mpr h4
  rw [hS_eq, card_weightSet W hW, if_pos h4W]
  by_cases h2 : 2 ∈ W
  · rw [if_pos h2]
    by_cases h6 : 6 ∈ W
    · rw [if_pos h6]; decide
    · rw [if_neg h6]; decide
  · rw [if_neg h2]
    by_cases h6 : 6 ∈ W
    · rw [if_pos h6]; decide
    · rw [if_neg h6]; decide

theorem card_weightClosed_of_six {S : Set (Fin 7 → ZMod 2)}
    (hS : ∀ v ∈ S, IsEvenVec v ∧ v ≠ 0)
    (hcl : ∀ v ∈ S, ∀ w : Fin 7 → ZMod 2, IsEvenVec w → vecWeight w = vecWeight v → w ∈ S)
    (h6 : ∃ v ∈ S, vecWeight v = 6) (h4 : ∀ v ∈ S, vecWeight v ≠ 4) :
    Nat.card S = 7 ∨ Nat.card S = 28 := by
  classical
  set W : Set ℕ := {k | ∃ v ∈ S, vecWeight v = k} with hWdef
  have hmem : ∀ k, k ∈ W ↔ ∃ v, v ∈ S ∧ vecWeight v = k := by
    intro k
    rw [hWdef]
    rfl
  have hS_eq : S = {v | IsEvenVec v ∧ vecWeight v ∈ W} := by
    ext v
    constructor
    · intro hv
      exact ⟨(hS v hv).1, (hmem (vecWeight v)).mpr ⟨v, hv, rfl⟩⟩
    · rintro ⟨hv, hmem_v⟩
      obtain ⟨u, hu, hwu⟩ := (hmem (vecWeight v)).mp hmem_v
      exact hcl u hu v hv hwu.symm
  have hW : ∀ k ∈ W, k = 2 ∨ k = 4 ∨ k = 6 := by
    intro k hk
    obtain ⟨v, hv, hwv⟩ := (hmem k).mp hk
    have hev : IsEvenVec v := (hS v hv).1
    have hv0 : v ≠ 0 := (hS v hv).2
    rcases vecWeight_cases_of_isEvenVec hev with h0 | h2 | h4' | h6'
    · exact absurd (eq_zero_of_vecWeight_eq_zero h0) hv0
    · exact Or.inl (hwv ▸ h2)
    · exact Or.inr (Or.inl (hwv ▸ h4'))
    · exact Or.inr (Or.inr (hwv ▸ h6'))
  have h6W : 6 ∈ W := (hmem 6).mpr h6
  have h4W : 4 ∉ W := by
    rintro hmem4
    obtain ⟨v, hv, hwv⟩ := (hmem 4).mp hmem4
    exact h4 v hv hwv
  rw [hS_eq, card_weightSet W hW, if_pos h6W, if_neg h4W]
  by_cases h2 : 2 ∈ W
  · rw [if_pos h2]; decide
  · rw [if_neg h2]; decide

end CFSG.OddStandard.SmallF3.Omega
