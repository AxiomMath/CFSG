module

public import CFSG.ClassicalInvolution.Q3.Q3TWCollGen
public import CFSG.ClassicalInvolution.Q3.Q3TWWordsTD

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.Q3Z

@[expose] def ext12 : Fin 12 → Fin 16 := fun i => ⟨i.val, by have := i.isLt; omega⟩

@[expose] def a2Idx16 : Fin 6 → Fin 16 := ![4, 5, 6, 7, 9, 10]

@[expose] def su4Idx : Fin 12 → Fin 16 := ![0, 1, 9, 10, 2, 3, 8, 11, 12, 13, 14, 15]

@[expose] def commWordsTD : List (List (Fin 16 × Bool)) :=
  [
  [(4, false), (8, false), (4, true), (8, true)], [(4, false), (11, false), (4, true), (11, true)],
  [(4, false), (12, false), (4, true), (12, true)],
  [(4, false), (13, false), (4, true), (13, true)], [(5, false), (8, false), (5, true), (8, true)],
  [(5, false), (11, false), (5, true), (11, true)],
  [(5, false), (12, false), (5, true), (12, true)],
  [(5, false), (13, false), (5, true), (13, true)]
  ]

@[expose] def substLetter16 (a b : List (Fin 16 × Bool)) (p : Fin 16 × Bool) :
    List (Fin 16 × Bool) :=
  if p.1 = 9 then (if p.2 then a else invWord a)
  else if p.1 = 10 then (if p.2 then b else invWord b) else [p]

@[expose] def td4GluedWords (a b : List (Fin 16 × Bool)) : List (List (Fin 16 × Bool)) :=
  a2Words.map (mapWord a2Idx16) ++
    su4Words.map (fun w => (mapWord su4Idx w).flatMap (substLetter16 a b)) ++ commWordsTD

@[expose] def td4aWords (k : Fin 24) : List (List (Fin 16 × Bool)) :=
  td4GluedWords (mapWord ext12 (gluingA k)) (mapWord ext12 (gluingB k))

@[expose] def TD4Collapse : Prop :=
  ∀ k : Fin 24, gluingComplete k = false → ∀ {G : Type} [Group G] (g : Fin 16 → G),
    RelsHold g (td4aWords k) → ∀ i, g i = 1

@[expose] def td4CollSet : Fin 24 → List ℕ :=
  ![
  [], [], [], [], [5, 12, 13], [5, 12, 13], [4, 8, 11], [4, 8, 11], [4, 12, 13], [4, 8, 10, 11],
  [5, 8, 11], [0, 8, 9, 11], [1, 9, 12, 13], [5, 9, 12, 13], [4, 12, 13], [4, 8, 10, 11],
  [5, 8, 11], [5, 8, 9, 11], [4, 10, 12, 13], [4, 10, 12, 13], [4, 12, 13], [4, 8, 11], [4, 10],
  [4, 12, 13]
  ]

@[expose] def td4CollCoef : Fin 16 → List (ℕ × ℤ) :=
  ![
  [(71, 1)], [(87, 1)], [(25, 1), (155, -1)], [(71, 1), (55, 1)], [(0, 1), (16, 1)], [(15, -1)],
  [(6, -1)], [(5, 1), (11, 1)], [(27, 1), (145, -1)], [(12, -1)], [(3, 1), (9, 1)],
  [(71, 1), (61, -1)], [(29, 1), (147, -1)], [(87, 1), (59, -1)], [(31, 1), (161, -1)],
  [(87, 1), (65, 1)]
  ]

@[expose] def td4CollapseCheck : Bool :=
  (List.finRange 24).all fun k =>
    gluingComplete k || subsetCheck (td4aWords k) (td4CollSet k) 400000 1

@[expose] def TD4CollapseCheck : Prop := td4CollapseCheck = true

theorem td4CollCommOK :
    ∀ k : Fin 24, gluingComplete k = true ∨ commOK (td4aWords k) (td4CollSet k) = true := by
  decide +kernel

theorem td4CollLatticeOK : ∀ k : Fin 24, latticeOK td4CollCoef (td4aWords k) = true := by
  decide +kernel

theorem td4Collapse_of_check (h : TD4CollapseCheck) : TD4Collapse := by
  intro k hk G _ g hg i
  have hall := List.all_eq_true.mp h k (List.mem_finRange k)
  rw [hk, Bool.false_or] at hall
  have hcomm := (td4CollCommOK k).resolve_left (by simp [hk])
  exact eq_one_of_fastCheck hall hcomm (td4CollLatticeOK k) g hg i

end CFSG.ClassicalInvolution.Q3.Q3TW
