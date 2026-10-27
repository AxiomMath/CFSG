module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.HubCases
public import CFSG.LieType.Universal.Spin.Roots.TypeB

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses

open CFSG.LieType.Universal.Spin

theorem cartanB_apply_eq_zero_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    cartanB m i j = 0 ↔ ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  simp only [cartanB, Matrix.of_apply, hij, ite_false]
  split_ifs with h h' <;> simp_all

theorem exists_nonadjacent_nat_B {m i j : ℕ} (hm : 4 ≤ m)
    (hj : j = i ∨ (i + 1 = j ∨ j + 1 = i)) :
    ∃ k : ℕ, k < m ∧ k ≠ i ∧ k ≠ j ∧ ¬ (i + 1 = k ∨ k + 1 = i) := by
  by_contra hcon
  have h0 : 0 < m → 0 ≠ i → 0 ≠ j → (i + 1 = 0 ∨ 0 + 1 = i) := fun a b c => by
    by_contra h; exact hcon ⟨0, a, b, c, h⟩
  have h1 : 1 < m → 1 ≠ i → 1 ≠ j → (i + 1 = 1 ∨ 1 + 1 = i) := fun a b c => by
    by_contra h; exact hcon ⟨1, a, b, c, h⟩
  have h2 : 2 < m → 2 ≠ i → 2 ≠ j → (i + 1 = 2 ∨ 2 + 1 = i) := fun a b c => by
    by_contra h; exact hcon ⟨2, a, b, c, h⟩
  have h3 : 3 < m → 3 ≠ i → 3 ≠ j → (i + 1 = 3 ∨ 3 + 1 = i) := fun a b c => by
    by_contra h; exact hcon ⟨3, a, b, c, h⟩
  omega

theorem exists_orthogonal_cartanB {m : ℕ} (hm : 4 ≤ m) {i j : Fin m}
    (hj : j = i ∨ cartanB m i j * cartanB m j i = 1) :
    ∃ k : Fin m, k ≠ i ∧ k ≠ j ∧ cartanB m i k = 0 := by
  have hj' : j.val = i.val ∨ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    rcases hj with rfl | hprod
    · exact Or.inl rfl
    · right
      by_cases hij : i = j
      · subst hij
        simp [cartanB] at hprod
      · by_contra hc
        have h0 : cartanB m i j = 0 := (cartanB_apply_eq_zero_iff hij).2 hc
        rw [h0] at hprod
        simp at hprod
  obtain ⟨k, hk, hki, hkj, hadj⟩ := exists_nonadjacent_nat_B hm hj'
  refine ⟨⟨k, hk⟩, fun h => hki (congrArg Fin.val h), fun h => hkj (congrArg Fin.val h), ?_⟩
  have hne : i ≠ ⟨k, hk⟩ := fun h => hki (congrArg Fin.val h).symm
  exact (cartanB_apply_eq_zero_iff hne).2 hadj

theorem hubCases_cartanB_three : HubCases (cartanB 3) := by
  have key1 : ∀ i : Fin 3,
      (∃ k : Fin 3, k ≠ i ∧ i ≠ k ∧ cartanB 3 i k = 0) ∨
      (∃ s : Fin 3, i ≠ s ∧ cartanB 3 i s = -1 ∧ cartanB 3 s i = -2 ∧ s ≠ i) := by
    intro i
    fin_cases i
    · exact Or.inl ⟨2, by decide⟩
    · exact Or.inr ⟨2, by decide⟩
    · exact Or.inl ⟨0, by decide⟩
  have key2 : ∀ i j : Fin 3, j ≠ i → cartanB 3 i j * cartanB 3 j i = 1 →
      (∃ k : Fin 3, (k ≠ i ∧ k ≠ j) ∧ i ≠ k ∧ cartanB 3 i k = 0) ∨
      (∃ s : Fin 3, i ≠ s ∧ cartanB 3 i s = -1 ∧ cartanB 3 s i = -2 ∧ (s ≠ i ∧ s ≠ j)) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first
      | exact fun h => absurd rfl h
      | exact fun _ h => absurd h (by decide)
      | exact fun _ _ => Or.inl ⟨2, by decide⟩
      | exact fun _ _ => Or.inr ⟨2, by decide⟩
  intro I i hi hex hI
  rcases hI with rfl | ⟨j, hji, rfl, hj⟩
  · rcases key1 i with ⟨k, hk, h1, h2⟩ | ⟨s, h1, h2, h3, hs⟩
    · exact Or.inl ⟨k, by simpa using hk, h1, h2⟩
    · exact Or.inr (Or.inr ⟨s, h1, h2, h3, by simpa using hs⟩)
  · rcases key2 i j hji hj with ⟨k, hk, h1, h2⟩ | ⟨s, h1, h2, h3, hs⟩
    · exact Or.inl ⟨k, by simpa [not_or] using hk, h1, h2⟩
    · exact Or.inr (Or.inr ⟨s, h1, h2, h3, by simpa [not_or] using hs⟩)

theorem hubCases_cartanB {m : ℕ} (hm : 3 ≤ m) : HubCases (cartanB m) := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hm4
  · exact hubCases_cartanB_three
  · intro I i hi hex hI
    rcases hI with rfl | ⟨j, hji, rfl, hj⟩
    · obtain ⟨k, hk, hk2, h0⟩ := exists_orthogonal_cartanB (by omega) (i := i) (j := i) (Or.inl rfl)
      exact Or.inl ⟨k, by simpa using hk, Ne.symm hk, h0⟩
    · obtain ⟨k, hk, hk2, h0⟩ := exists_orthogonal_cartanB (by omega) (i := i) (j := j) (Or.inr hj)
      exact Or.inl ⟨k, by simp [hk, hk2], Ne.symm hk, h0⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses
