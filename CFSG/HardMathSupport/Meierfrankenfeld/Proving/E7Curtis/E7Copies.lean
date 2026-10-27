module

public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Weyl

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

@[expose] def finWord (l : List ℕ) : List (Fin Tag.E7.rank) :=
  l.map fun c => ⟨c % 7, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
@[expose] def copyWordsE7 : List (List (List (Fin Tag.E7.rank))) :=
[
  [finWord [],
   finWord [3, 4, 2, 3, 1, 3, 2, 4, 3],
   finWord [5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5],
   finWord [3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3],
   finWord [6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6],
   finWord [4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4],
   finWord [5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5],
   finWord [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2],
   finWord [6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6],
   finWord [6, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 6],
   finWord [4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4],
   finWord [5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5],
   finWord [5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5],
   finWord [6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6],
   finWord [6, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 6],
   finWord [4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4],
   finWord [5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5],
   finWord [6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6],
   finWord [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5],
   finWord [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3],
   finWord [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2]],
  [finWord [],
   finWord [3, 2, 0, 2, 3],
   finWord [4, 3, 2, 0, 2, 3, 4],
   finWord [1, 3, 2, 0, 2, 3, 1],
   finWord [3, 4, 2, 3, 1, 3, 2, 4, 3],
   finWord [5, 4, 3, 2, 0, 2, 3, 4, 5],
   finWord [4, 1, 3, 2, 0, 2, 3, 1, 4],
   finWord [5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5],
   finWord [6, 5, 4, 3, 2, 0, 2, 3, 4, 5, 6],
   finWord [5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5],
   finWord [6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6],
   finWord [4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4],
   finWord [6, 5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5, 6],
   finWord [6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6],
   finWord [5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5],
   finWord [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3],
   finWord [6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6],
   finWord [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1],
   finWord [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5],
   finWord [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6],
   finWord [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4]],
  [finWord [],
   finWord [4, 3, 2, 3, 4],
   finWord [4, 3, 1, 3, 4],
   finWord [2, 3, 1, 3, 2],
   finWord [5, 4, 3, 2, 3, 4, 5],
   finWord [5, 4, 3, 1, 3, 4, 5],
   finWord [4, 3, 2, 0, 2, 3, 4],
   finWord [1, 3, 2, 0, 2, 3, 1],
   finWord [6, 5, 4, 3, 2, 3, 4, 5, 6],
   finWord [6, 5, 4, 3, 1, 3, 4, 5, 6],
   finWord [5, 4, 3, 2, 0, 2, 3, 4, 5],
   finWord [6, 5, 4, 3, 2, 0, 2, 3, 4, 5, 6],
   finWord [4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4],
   finWord [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2],
   finWord [6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6],
   finWord [4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4],
   finWord [5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5],
   finWord [5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5],
   finWord [6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6],
   finWord [6, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 6],
   finWord [5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5]],
  [finWord [],
   finWord [5, 4, 3, 4, 5],
   finWord [6, 5, 4, 3, 4, 5, 6],
   finWord [5, 4, 3, 2, 3, 4, 5],
   finWord [5, 4, 3, 1, 3, 4, 5],
   finWord [6, 5, 4, 3, 2, 3, 4, 5, 6],
   finWord [6, 5, 4, 3, 1, 3, 4, 5, 6],
   finWord [5, 4, 2, 3, 1, 3, 2, 4, 5],
   finWord [3, 4, 2, 3, 1, 3, 2, 4, 3],
   finWord [5, 4, 3, 2, 0, 2, 3, 4, 5],
   finWord [6, 5, 4, 2, 3, 1, 3, 2, 4, 5, 6],
   finWord [6, 5, 4, 3, 2, 0, 2, 3, 4, 5, 6],
   finWord [5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5],
   finWord [3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3],
   finWord [6, 5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5, 6],
   finWord [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2],
   finWord [5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5],
   finWord [5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5],
   finWord [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3],
   finWord [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5],
   finWord [6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6]],
  [finWord [],
   finWord [6, 5, 4, 5, 6],
   finWord [6, 5, 4, 3, 4, 5, 6],
   finWord [6, 5, 4, 3, 2, 3, 4, 5, 6],
   finWord [6, 5, 4, 3, 1, 3, 4, 5, 6],
   finWord [6, 5, 4, 2, 3, 1, 3, 2, 4, 5, 6],
   finWord [6, 5, 4, 3, 2, 0, 2, 3, 4, 5, 6],
   finWord [6, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 6],
   finWord [4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4],
   finWord [6, 5, 4, 1, 3, 2, 0, 2, 3, 1, 4, 5, 6],
   finWord [6, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 6],
   finWord [4, 5, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 5, 4],
   finWord [6, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 6],
   finWord [4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4],
   finWord [3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3],
   finWord [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1],
   finWord [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4],
   finWord [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4],
   finWord [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3],
   finWord [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2],
   finWord [0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0]]
]

@[expose] def copyWordE7 (s : Fin 5) (i : Fin 21) : List (Fin Tag.E7.rank) :=
  ((copyWordsE7.getD s []).getD i [])

theorem copyWordsE7_check : ∀ s : Fin 5, ∀ i : Fin 21,
    (copyWordE7 s i).foldr reflectL7 (List.ofFn (Pi.single (node5 s) (1 : ℤ))) =
      List.ofFn (Pi.single (node5 s) (1 : ℤ)) ∧
    ∀ j : Fin 21, i ≠ j →
      (copyWordE7 s i).foldr reflectL7 (List.ofFn (e7Omega2 (node5 s))) ≠
        (copyWordE7 s j).foldr reflectL7 (List.ofFn (e7Omega2 (node5 s))) := by
  decide +kernel

theorem exists_copyWeyl_e7
    (s : Fin Tag.E7.rank) (hs : 1 ≤ s.val ∧ s.val ≤ 5) :
    ∃ u : Fin 21 → WeylGroup .E7,
      (∀ i, u i • (Pi.single s (1 : ℤ) : Fin Tag.E7.rank → ℤ) = Pi.single s (1 : ℤ)) ∧
      ∀ i j, i ≠ j → u i • e7Omega2 s ≠ u j • e7Omega2 s := by
  obtain ⟨s', rfl⟩ : ∃ s' : Fin 5, node5 s' = s := by
    refine ⟨⟨s.val - 1, by omega⟩, Fin.ext ?_⟩
    simp only [node5]
    omega
  refine ⟨fun i => (coxeterSystem .E7).wordProd (copyWordE7 s' i), ?_, ?_⟩
  · intro i
    rw [wordProd_smul']
    apply List.ofFn_injective
    rw [ofFn_foldr_reflect7]
    exact (copyWordsE7_check s' i).1
  · intro i j hij h
    rw [wordProd_smul', wordProd_smul'] at h
    have h2 := congrArg (fun v => List.ofFn v) h
    simp only [ofFn_foldr_reflect7] at h2
    exact (copyWordsE7_check s' i).2 j hij (by simpa [ofFn_foldr_reflect7] using h2)

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
