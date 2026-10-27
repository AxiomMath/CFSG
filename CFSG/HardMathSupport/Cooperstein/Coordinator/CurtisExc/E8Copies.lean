module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Weyl

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

@[expose] def copyWords : List (List (List (Fin Tag.E8.rank))) :=
  ([
  [[], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2], [5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5], [6, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 6], [4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4]],
  [[], [3, 4, 2, 3, 1, 3, 2, 4, 3], [5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5], [3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3], [6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6]],
  [[], [3, 2, 0, 2, 3], [4, 3, 2, 0, 2, 3, 4], [1, 3, 2, 0, 2, 3, 1], [3, 4, 2, 3, 1, 3, 2, 4, 3]],
  [[], [4, 3, 2, 3, 4], [4, 3, 1, 3, 4], [2, 3, 1, 3, 2], [5, 4, 3, 2, 3, 4, 5]],
  [[], [5, 4, 3, 4, 5], [6, 5, 4, 3, 4, 5, 6], [5, 4, 3, 2, 3, 4, 5], [5, 4, 3, 1, 3, 4, 5]],
  [[], [6, 5, 4, 5, 6], [7, 6, 5, 4, 5, 6, 7], [6, 5, 4, 3, 4, 5, 6], [7, 6, 5, 4, 3, 4, 5, 6, 7]],
  [[], [7, 6, 5, 6, 7], [7, 6, 5, 4, 5, 6, 7], [7, 6, 5, 4, 3, 4, 5, 6, 7], [7, 6, 5, 4, 3, 2, 3, 4, 5, 6, 7]],
  [[], [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6], [6, 7, 5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5, 7, 6], [6, 7, 5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5, 7, 6], [6, 7, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 7, 6]]] : List (List (List (Fin 8))))

theorem copyWords_check : ∀ s : Fin Tag.E8.rank, ∀ i : Fin 5,
    ((copyWords.getD s []).getD i []).foldr reflectL (List.ofFn (Pi.single s (1 : ℤ))) =
        List.ofFn (Pi.single s (1 : ℤ)) ∧
      ∀ j : Fin 5, i ≠ j →
        ((copyWords.getD s []).getD i []).foldr reflectL (List.ofFn (e8Omega s)) ≠
          ((copyWords.getD s []).getD j []).foldr reflectL (List.ofFn (e8Omega s)) := by
  decide +kernel

theorem exists_copyWeyl
    (s : Fin Tag.E8.rank) :
    ∃ u : Fin 5 → WeylGroup .E8, (∀ i, u i • (Pi.single s 1 : Fin Tag.E8.rank → ℤ) = Pi.single s 1) ∧
      ∀ i j, i ≠ j → u i • e8Omega s ≠ u j • e8Omega s := by
  refine ⟨fun i => (coxeterSystem .E8).wordProd ((copyWords.getD s []).getD i []), fun i => ?_,
    fun i j hij h => ?_⟩
  · rw [wordProd_smul']
    refine List.ofFn_injective ?_
    rw [ofFn_foldr_reflect]
    exact (copyWords_check s i).1
  · rw [wordProd_smul', wordProd_smul'] at h
    have h2 := congrArg List.ofFn h
    rw [ofFn_foldr_reflect, ofFn_foldr_reflect] at h2
    exact (copyWords_check s i).2 j hij h2

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
