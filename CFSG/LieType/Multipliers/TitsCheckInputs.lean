module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Sporadic.Schreier.TitsArrays
public import CFSG.Sporadic.Schreier.TitsBasic

@[expose] public section

namespace CFSG.LieType.Multipliers.Tits

open CFSG.CosetTable CFSG.Sporadic.Schreier.Tits

def powW {m : ℕ} (w : List (Fin m × Bool)) (k : ℕ) : List (Fin m × Bool) :=
  (List.replicate k w).flatten

abbrev la : List (Fin 3 × Bool) := [(0, true)]

abbrev lb : List (Fin 3 × Bool) := [(1, true)]

abbrev lB : List (Fin 3 × Bool) := [(1, false)]

abbrev lc : List (Fin 3 × Bool) := [(2, true)]

abbrev lC : List (Fin 3 × Bool) := [(2, false)]

def titsRels : List (List (Fin 3 × Bool)) :=
  [powW la 2, powW lb 3, powW (la ++ lb) 13, powW (commWord la lb) 5,
    powW (commWord la (lb ++ la ++ lb)) 4, powW (powW (la ++ lb) 4 ++ la ++ lB) 6,
    lC ++ la ++ lb ++ la ++ lb ++ la ++ lB ++ la,
    powW lb 3, powW lc 3, powW (lc ++ lB) 4, powW (lC ++ lB) 8,
    lb ++ lc ++ lb ++ lc ++ lb ++ lC ++ lB ++ lC ++ lB ++ lC ++ lb ++ lc ++ lb ++ lc ++ lB ++
      lC ++ lB ++ lC ++ lB ++ lc]

def titsComm : Fin 3 → List (List (Fin 3 × Bool) × List (Fin 3 × Bool))
  | 0 => [(lB, lC ++ lb ++ la ++ lC), (lB ++ lC ++ lb ++ la, lb ++ lc ++ lb ++ lc)]
  | 1 => [(lC ++ lB ++ lC ++ lB ++ lc ++ lB, lC ++ lB ++ lC ++ lB ++ lC ++ lB ++ lc)]
  | 2 => [(lb ++ lc ++ lb ++ lc ++ lb ++ lc ++ lB, lb ++ lc ++ lb ++ lc ++ lB ++ lc)]

def titsCommWord (i : Fin 3) : List (Fin 3 × Bool) := commWords (titsComm i)

abbrev titsCoverWords : List (List (Fin 3 × Bool)) := coverWords titsRels titsCommWord

abbrev titsRelsBC := restrictWords (subsetOf 3 [1, 2]) titsRels

abbrev titsCoverWordsBC := restrictWords (subsetOf 3 [1, 2]) titsCoverWords

def zword {m : ℕ} (w : List (Fin m × Bool)) : List ℤ :=
  w.map fun l => if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

def invZ (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

def titsAWord : List ℤ := (List.replicate 5 [1, 1, -2]).flatten

def titsBWord : List ℤ := [-1, -1, -2, -1, 2, 2, 1, 2, 1, 1]

def abcWords : List (List ℤ) :=
  [titsAWord, titsBWord, titsAWord ++ titsBWord ++ titsAWord ++ titsBWord ++ titsAWord ++
    invZ titsBWord ++ titsAWord]

def abcArrs : Array (Array ℕ) :=
  Array.ofFn (n := 3) fun i => wordArr 1755 titsDerivedArrs (abcWords.getD i.val [])

def titsDWords : List (List ℤ) :=
  [[-2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2,
      1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1],
    [1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2,
      1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2,
      1]]

def titsOneWords : List (List (Fin 3 × Bool)) :=
  titsRels ++ (List.finRange 3).map fun i => [(i, false)] ++ titsCommWord i

end CFSG.LieType.Multipliers.Tits
