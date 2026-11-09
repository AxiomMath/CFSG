module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Family

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Blueprint.Chevalley

@[expose] def betaD (s : Fin Tag.F4.rank) (i i' j j' : ℕ) (c : Fin Tag.F4.rank) : ℤ :=
  (betaL s i j).getD c 0 - (betaL s i' j').getD c 0

@[expose] def gamD (s : Fin Tag.F4.rank) (i i' : ℕ) (c : Fin Tag.F4.rank) : ℤ :=
  (gamL s i).getD c 0 - (gamL s i').getD c 0

abbrev PairCasesAt (s : Fin Tag.F4.rank) (i i' : Fin 12) : Prop :=
  ∀ (j j' : Fin 8),
    (1 ≤ contentL (minorsL (List.ofFn (betaD s i i' j j')) (List.ofFn (gamD s i i'))) ∧
      contentL (minorsL (List.ofFn (betaD s i i' j j')) (List.ofFn (gamD s i i'))) ≤ 6) ∨
    (1 ≤ contentL (List.ofFn (gamD s i i')) ∧ contentL (List.ofFn (gamD s i i')) ≤ 2 ∧
      ((∀ c, betaD s i i' j j' c = gamD s i i' c) ∨ (∀ c, betaD s i i' j j' c = - gamD s i i' c) ∨
        (∀ c, betaD s i i' j j' c = 2 * gamD s i i' c) ∨ (∀ c, betaD s i i' j j' c = 0)))

theorem pair_cases_0a : ∀ i i' : Fin 12, i.val < 6 → i ≠ i' → PairCasesAt (f4n 0) i i' := by
  decide +kernel

theorem pair_cases_0b : ∀ i i' : Fin 12, 6 ≤ i.val → i ≠ i' → PairCasesAt (f4n 0) i i' := by
  decide +kernel

theorem pair_cases_3a : ∀ i i' : Fin 12, i.val < 6 → i ≠ i' → PairCasesAt (f4n 3) i i' := by
  decide +kernel

theorem pair_cases_3b : ∀ i i' : Fin 12, 6 ≤ i.val → i ≠ i' → PairCasesAt (f4n 3) i i' := by
  decide +kernel

theorem pair_cases : ∀ (s : Fin Tag.F4.rank), (s.val = 0 ∨ s.val = 3) → ∀ (i i' : Fin 12), i ≠ i' →
    ∀ (j j' : Fin 8),
    (1 ≤ contentL (minorsL (List.ofFn (betaD s i i' j j')) (List.ofFn (gamD s i i'))) ∧
      contentL (minorsL (List.ofFn (betaD s i i' j j')) (List.ofFn (gamD s i i'))) ≤ 6) ∨
    (1 ≤ contentL (List.ofFn (gamD s i i')) ∧ contentL (List.ofFn (gamD s i i')) ≤ 2 ∧
      ((∀ c, betaD s i i' j j' c = gamD s i i' c) ∨ (∀ c, betaD s i i' j j' c = - gamD s i i' c) ∨
        (∀ c, betaD s i i' j j' c = 2 * gamD s i i' c) ∨ (∀ c, betaD s i i' j j' c = 0))) := by
  intro s hs i i' hii'
  have hs' : s = f4n 0 ∨ s = f4n 3 := by
    rcases hs with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hs' with rfl | rfl
  · by_cases hi : i.val < 6
    · exact pair_cases_0a i i' hi hii'
    · exact pair_cases_0b i i' (by omega) hii'
  · by_cases hi : i.val < 6
    · exact pair_cases_3a i i' hi hii'
    · exact pair_cases_3b i i' (by omega) hii'

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
