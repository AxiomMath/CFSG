module

public import CFSG.ClassicalInvolution.Q3.Q3TWCollGen

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.Q3Z

@[expose] def b2Idx : Fin 8 → Fin 12 := ![0, 1, 9, 10, 2, 3, 8, 11]

@[expose] def commWordsB : List (List (Fin 12 × Bool)) :=
  [[(4, false), (3, false), (4, true), (3, true)], [(4, false), (8, false), (4, true), (8, true)],
  [(5, false), (3, false), (5, true), (3, true)], [(5, false), (8, false), (5, true), (8, true)]]

@[expose] def b3GluedWords (a b : List (Fin 12 × Bool)) : List (List (Fin 12 × Bool)) :=
  a2Words.map (mapWord a2Idx) ++
    c2Words.map (fun w => (mapWord b2Idx w).flatMap (substLetter a b)) ++ commWordsB

@[expose] def b3aWords (k : Fin 24) : List (List (Fin 12 × Bool)) :=
  b3GluedWords (gluingA k) (gluingB k)

@[expose] def B3Collapse : Prop :=
  ∀ k : Fin 24, gluingComplete k = false → ∀ {G : Type} [Group G] (g : Fin 12 → G),
    RelsHold g (b3aWords k) → ∀ i, g i = 1

@[expose] def b3CollSet : Fin 24 → List ℕ :=
  ![
  [], [], [], [], [5, 8], [7, 10], [7, 10], [4, 8], [3, 5], [3, 4, 10], [3, 5], [3, 5, 9], [3, 5],
  [7, 10], [3, 4], [3, 4, 10], [7, 10], [3, 5, 9], [4, 8, 10], [5, 8], [7, 10], [4, 8], [3, 4],
  [5, 8]
  ]

@[expose] def b3CollCoef : Fin 12 → List (ℕ × ℤ) :=
  ![
  [(49, -1)], [(52, -1)], [(25, 1), (42, 1), (49, -1)], [(26, 1), (45, 1), (49, -2)],
  [(0, 1), (16, 1)], [(15, -1)], [(6, -1)], [(5, 1), (11, 1)], [(44, -1), (52, 2)], [(12, -1)],
  [(3, 1), (9, 1)], [(47, -1), (52, 1)]
  ]

@[expose] def b3CollapseCheck : Bool :=
  (List.finRange 24).all fun k =>
    gluingComplete k || subsetCheck (b3aWords k) (b3CollSet k) 200000 1

@[expose] def B3CollapseCheck : Prop := b3CollapseCheck = true

theorem b3CollCommOK :
    ∀ k : Fin 24, gluingComplete k = true ∨ commOK (b3aWords k) (b3CollSet k) = true := by
  decide +kernel

theorem b3CollLatticeOK : ∀ k : Fin 24, latticeOK b3CollCoef (b3aWords k) = true := by
  decide +kernel

theorem b3Collapse_of_check (h : B3CollapseCheck) : B3Collapse := by
  intro k hk G _ g hg i
  have hall := List.all_eq_true.mp h k (List.mem_finRange k)
  rw [hk, Bool.false_or] at hall
  have hcomm := (b3CollCommOK k).resolve_left (by simp [hk])
  exact eq_one_of_fastCheck hall hcomm (b3CollLatticeOK k) g hg i

end CFSG.ClassicalInvolution.Q3.Q3TW
