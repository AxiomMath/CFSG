module

public section

namespace CFSG.EvenSporadicStandard.M22Std.TabCheck

abbrev Tab : Type := List Nat

@[expose] def idTab : Tab := List.range 22

@[expose] def tmul (s t : Tab) : Tab := t.map fun j => s.getD j 0

@[expose] def wordTab (ts : List Tab) : List Nat → Tab
  | [] => idTab
  | i :: w => tmul (ts.getD i idTab) (wordTab ts w)

@[expose] def ext (sp : List Tab) (g : Tab) : List Tab := sp ++ sp.map (tmul g)

@[expose] def span : List Tab → List Tab
  | [] => [idTab]
  | g :: gs => ext (span gs) g

@[expose] def isInv (t : Tab) : Bool := decide (t ≠ idTab ∧ tmul t t = idTab)

@[expose] def comm (s t : Tab) : Bool := decide (tmul s t = tmul t s)

@[expose] def sylowOK (gs : List Tab) : Bool :=
  decide ((span gs).length = 128 ∧ (span gs).Nodup ∧ ∀ l ∈ span gs, ∀ g ∈ gs, tmul l g ∈ span gs)

@[expose] def elemAbOK (L : List Tab) (As : List (List Tab)) : Bool :=
  let I := L.filter isInv
  I.all fun a =>
    let Ia := I.filter (comm a)
    let P1 := ext [idTab] a
    Ia.all fun b =>
      if decide (b ∉ P1) then
        let Ib := Ia.filter (comm b)
        let P2 := ext P1 b
        Ib.all fun c =>
          if decide (c ∉ P2) then
            let Ic := Ib.filter (comm c)
            let P3 := ext P2 c
            Ic.all fun d =>
              if decide (d ∉ P3) then
                let P4 := ext P3 d
                As.any fun A => A.all fun y => decide (y ∈ P4)
              else true
          else true
      else true

@[expose] def tabA : Tab :=
  [12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]

@[expose] def tabB : Tab :=
  [21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]

@[expose] def tabBi : Tab := tmul tabB (tmul tabB tabB)

@[expose] def letterTabs : List Tab := [tabA, tabB, tabBi]

@[expose] def sylowWords : List (List Nat) :=
  [
    [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2],
    [0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0],
    [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0],
    [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 1],
    [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0],
    [2, 0, 1]
  ]

@[expose] def gensTab : List Tab := sylowWords.map (wordTab letterTabs)

@[expose] def elemWordsList : List (List (List Nat)) :=
  [
    [
      [1, 5, 6],
      [0, 1, 2, 4, 6],
      [0, 4, 6],
      [2, 5, 6],
      [1, 2],
      [0, 1, 3, 4],
      [0, 2, 3, 4],
      [3, 6],
      [1, 3, 5],
      [0, 1, 2, 3, 4, 5, 6],
      [0, 3, 4, 5, 6],
      [2, 3, 5],
      [1, 2, 3, 6],
      [0, 1, 4, 5],
      [0, 2, 4, 5]
    ],
    [
      [2, 6],
      [3],
      [2, 5],
      [2, 5, 6],
      [3, 5, 6],
      [5, 6],
      [2, 3, 5, 6],
      [5],
      [6],
      [2, 3, 6],
      [3, 6],
      [2, 3, 5],
      [3, 5],
      [2],
      [2, 3]
    ]
  ]

@[expose] def elemWords (k : Fin 2) : List (List Nat) := elemWordsList.getD k.val []

@[expose] def elemTabs (k : Fin 2) : List Tab := (elemWords k).map (wordTab gensTab)

@[expose] def invsOK (T : List Tab) : Bool :=
  decide (T.length = 15 ∧ T.Nodup ∧ ∀ t ∈ T, t ≠ idTab ∧ tmul t t = idTab)

theorem invsOK_elemTabs : ∀ k : Fin 2, invsOK (elemTabs k) = true := by
  decide

end CFSG.EvenSporadicStandard.M22Std.TabCheck
