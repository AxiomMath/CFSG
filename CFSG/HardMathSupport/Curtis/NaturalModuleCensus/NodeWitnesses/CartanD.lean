module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.HubCases
public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses

open CFSG.LieType.Universal.Spin

theorem cartanD_apply_eq_zero_iff {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    cartanD n i j = 0 ↔ ¬ ((i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n)) := by
  simp only [cartanD, Matrix.of_apply, hij, ite_false]
  split_ifs with h <;> simp [h]

theorem exists_nonadjacent_nat {n i j : ℕ} (hn : 5 ≤ n) (hj : j = i ∨
    ((i + 1 = j ∧ j + 1 < n) ∨ (j + 1 = i ∧ i + 1 < n) ∨ (i + 3 = n ∧ j + 1 = n) ∨
      (j + 3 = n ∧ i + 1 = n))) :
    ∃ k : ℕ, k < n ∧ k ≠ i ∧ k ≠ j ∧ ¬ ((i + 1 = k ∧ k + 1 < n) ∨ (k + 1 = i ∧ i + 1 < n) ∨
      (i + 3 = n ∧ k + 1 = n) ∨ (k + 3 = n ∧ i + 1 = n)) := by
  by_contra hcon
  have h0 : 0 < n → 0 ≠ i → 0 ≠ j → ((i + 1 = 0 ∧ 0 + 1 < n) ∨ (0 + 1 = i ∧ i + 1 < n) ∨
      (i + 3 = n ∧ 0 + 1 = n) ∨ (0 + 3 = n ∧ i + 1 = n)) := fun a b c => by
    by_contra h; exact hcon ⟨0, a, b, c, h⟩
  have h1 : 1 < n → 1 ≠ i → 1 ≠ j → ((i + 1 = 1 ∧ 1 + 1 < n) ∨ (1 + 1 = i ∧ i + 1 < n) ∨
      (i + 3 = n ∧ 1 + 1 = n) ∨ (1 + 3 = n ∧ i + 1 = n)) := fun a b c => by
    by_contra h; exact hcon ⟨1, a, b, c, h⟩
  have h2 : 2 < n → 2 ≠ i → 2 ≠ j → ((i + 1 = 2 ∧ 2 + 1 < n) ∨ (2 + 1 = i ∧ i + 1 < n) ∨
      (i + 3 = n ∧ 2 + 1 = n) ∨ (2 + 3 = n ∧ i + 1 = n)) := fun a b c => by
    by_contra h; exact hcon ⟨2, a, b, c, h⟩
  have h3 : 3 < n → 3 ≠ i → 3 ≠ j → ((i + 1 = 3 ∧ 3 + 1 < n) ∨ (3 + 1 = i ∧ i + 1 < n) ∨
      (i + 3 = n ∧ 3 + 1 = n) ∨ (3 + 3 = n ∧ i + 1 = n)) := fun a b c => by
    by_contra h; exact hcon ⟨3, a, b, c, h⟩
  have h4 : 4 < n → 4 ≠ i → 4 ≠ j → ((i + 1 = 4 ∧ 4 + 1 < n) ∨ (4 + 1 = i ∧ i + 1 < n) ∨
      (i + 3 = n ∧ 4 + 1 = n) ∨ (4 + 3 = n ∧ i + 1 = n)) := fun a b c => by
    by_contra h; exact hcon ⟨4, a, b, c, h⟩
  omega

theorem exists_orthogonal_cartanD {n : ℕ} (hn : 5 ≤ n) {i j : Fin n}
    (hj : j = i ∨ cartanD n i j * cartanD n j i = 1) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ cartanD n i k = 0 := by
  have hj' : j.val = i.val ∨
      ((i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
        (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n)) := by
    rcases hj with rfl | hprod
    · exact Or.inl rfl
    · right
      by_cases hij : i = j
      · subst hij
        simp [cartanD] at hprod
      · by_contra hc
        have h0 : cartanD n i j = 0 := (cartanD_apply_eq_zero_iff hij).2 hc
        rw [h0] at hprod
        simp at hprod
  obtain ⟨k, hk, hki, hkj, hadj⟩ := exists_nonadjacent_nat hn hj'
  refine ⟨⟨k, hk⟩, fun h => hki (congrArg Fin.val h), fun h => hkj (congrArg Fin.val h), ?_⟩
  have hne : i ≠ ⟨k, hk⟩ := fun h => hki (congrArg Fin.val h).symm
  exact (cartanD_apply_eq_zero_iff hne).2 hadj

theorem hubCases_cartanD_four : HubCases (cartanD 4) := by
  have key1 : ∀ i : Fin 4,
      (∃ k : Fin 4, k ≠ i ∧ i ≠ k ∧ cartanD 4 i k = 0) ∨
      (∃ a b k : Fin 4, a ≠ b ∧ cartanD 4 a i = -1 ∧ cartanD 4 i a = -1 ∧ cartanD 4 a b = 0 ∧
        k ≠ i ∧ 0 < (Pi.single b 1 - cartanD 4 i b • Pi.single i 1 -
          cartanD 4 i b • Pi.single a 1 : Fin 4 → ℤ) k) := by
    intro i
    fin_cases i
    · exact Or.inl ⟨2, by decide⟩
    · exact Or.inr ⟨0, 2, 2, by decide⟩
    · exact Or.inl ⟨0, by decide⟩
    · exact Or.inl ⟨0, by decide⟩
  have key2 : ∀ i j : Fin 4, j ≠ i → cartanD 4 i j * cartanD 4 j i = 1 →
      (∃ k : Fin 4, (k ≠ i ∧ k ≠ j) ∧ i ≠ k ∧ cartanD 4 i k = 0) ∨
      (∃ a b k : Fin 4, a ≠ b ∧ cartanD 4 a i = -1 ∧ cartanD 4 i a = -1 ∧ cartanD 4 a b = 0 ∧
        (k ≠ i ∧ k ≠ j) ∧ 0 < (Pi.single b 1 - cartanD 4 i b • Pi.single i 1 -
          cartanD 4 i b • Pi.single a 1 : Fin 4 → ℤ) k) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first
      | exact fun h => absurd rfl h
      | exact fun _ h => absurd h (by decide)
      | exact fun _ _ => Or.inl ⟨2, by decide⟩
      | exact fun _ _ => Or.inl ⟨0, by decide⟩
      | exact fun _ _ => Or.inr ⟨0, 2, 2, by decide⟩
      | exact fun _ _ => Or.inr ⟨0, 2, 0, by decide⟩
  intro I i hi hex hI
  rcases hI with rfl | ⟨j, hji, rfl, hj⟩
  · rcases key1 i with ⟨k, hk, h1, h2⟩ | ⟨a, b, k, h1, h2, h3, h4, hk, h5⟩
    · exact Or.inl ⟨k, by simpa using hk, h1, h2⟩
    · exact Or.inr (Or.inl ⟨a, b, k, h1, h2, h3, h4, by simpa using hk, h5⟩)
  · rcases key2 i j hji hj with ⟨k, hk, h1, h2⟩ | ⟨a, b, k, h1, h2, h3, h4, hk, h5⟩
    · exact Or.inl ⟨k, by simpa [not_or] using hk, h1, h2⟩
    · exact Or.inr (Or.inl ⟨a, b, k, h1, h2, h3, h4, by simpa [not_or] using hk, h5⟩)

theorem hubCases_cartanD {n : ℕ} (hn : 4 ≤ n) : HubCases (cartanD n) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · exact hubCases_cartanD_four
  · intro I i hi hex hI
    rcases hI with rfl | ⟨j, hji, rfl, hj⟩
    · obtain ⟨k, hk, hk2, h0⟩ := exists_orthogonal_cartanD (by omega) (i := i) (j := i) (Or.inl rfl)
      exact Or.inl ⟨k, by simpa using hk, Ne.symm hk, h0⟩
    · obtain ⟨k, hk, hk2, h0⟩ := exists_orthogonal_cartanD (by omega) (i := i) (j := j) (Or.inr hj)
      exact Or.inl ⟨k, by simp [hk, hk2], Ne.symm hk, h0⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses
