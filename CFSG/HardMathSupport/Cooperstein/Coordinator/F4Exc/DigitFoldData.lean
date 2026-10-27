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

theorem pair_cases : ∀ (s : Fin Tag.F4.rank), (s.val = 0 ∨ s.val = 3) → ∀ (i i' : Fin 12), i ≠ i' →
    ∀ (j j' : Fin 8),
    (1 ≤ contentL (minorsL (List.ofFn (betaD s i i' j j')) (List.ofFn (gamD s i i'))) ∧
      contentL (minorsL (List.ofFn (betaD s i i' j j')) (List.ofFn (gamD s i i'))) ≤ 6) ∨
    (1 ≤ contentL (List.ofFn (gamD s i i')) ∧ contentL (List.ofFn (gamD s i i')) ≤ 2 ∧
      ((∀ c, betaD s i i' j j' c = gamD s i i' c) ∨ (∀ c, betaD s i i' j j' c = - gamD s i i' c) ∨
        (∀ c, betaD s i i' j j' c = 2 * gamD s i i' c) ∨ (∀ c, betaD s i i' j j' c = 0))) := by
  decide +kernel

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
