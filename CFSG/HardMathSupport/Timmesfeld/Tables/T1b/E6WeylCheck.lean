module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.AGLEmbedding.R3

@[expose] def e6ReflL : List (List Nat) := [
  [2, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 0, 0,
   1, 0, 1, 0, 0, 0,
   0, 0, 0, 1, 0, 0,
   0, 0, 0, 0, 1, 0,
   0, 0, 0, 0, 0, 1],
  [1, 0, 0, 0, 0, 0,
   0, 2, 0, 0, 0, 0,
   0, 0, 1, 0, 0, 0,
   0, 1, 0, 1, 0, 0,
   0, 0, 0, 0, 1, 0,
   0, 0, 0, 0, 0, 1],
  [1, 0, 1, 0, 0, 0,
   0, 1, 0, 0, 0, 0,
   0, 0, 2, 0, 0, 0,
   0, 0, 1, 1, 0, 0,
   0, 0, 0, 0, 1, 0,
   0, 0, 0, 0, 0, 1],
  [1, 0, 0, 0, 0, 0,
   0, 1, 0, 1, 0, 0,
   0, 0, 1, 1, 0, 0,
   0, 0, 0, 2, 0, 0,
   0, 0, 0, 1, 1, 0,
   0, 0, 0, 0, 0, 1],
  [1, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 0, 0,
   0, 0, 1, 0, 0, 0,
   0, 0, 0, 1, 1, 0,
   0, 0, 0, 0, 2, 0,
   0, 0, 0, 0, 1, 1],
  [1, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 0, 0,
   0, 0, 1, 0, 0, 0,
   0, 0, 0, 1, 0, 0,
   0, 0, 0, 0, 1, 1,
   0, 0, 0, 0, 0, 2]]

@[expose] def e6WordL (ω : List Nat) : List Nat :=
  ω.foldr (fun i A => mmulL 3 6 (e6ReflL.getD i []) A) (midL 3 6)

@[expose] def e6SylWords : List (List Nat) :=
  [[3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3], [0, 2], [4, 5],
    [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1]]

@[expose] def e6SylL (_ : Unit := ()) : List (List Nat) :=
  wordsL 3 6 (e6SylWords.map e6WordL)

@[expose] def matVecA6 (Ma : Array Nat) (c : List Nat) : List Nat :=
  (List.range 6).map fun k =>
    ((List.range 6).foldl (fun s i => s + Ma.getD (6 * k + i) 0 * c.getD i 0) 0) % 3

@[expose] def nfix6 (A : List Nat) : Nat :=
  let Ma := A.toArray
  ((allVecs 3 6).filter fun v => matVecA6 Ma v == v).length

@[expose] def isO3L (A : List Nat) : Bool :=
  A != midL 3 6 && mmulL 3 6 (mmulL 3 6 A A) A == midL 3 6

@[expose] def e6SylCheck (_ : Unit := ()) : Bool :=
  let S := e6SylL ()
  let t := e6WordL (e6SylWords.getD 0 [])
  let c := e6WordL (e6SylWords.getD 1 [])
  let O := (S.filter isO3L).map fun A => nfix6 A
  S.length == 81 && decide S.Nodup &&
    S.all (fun A => S.all fun B => S.contains (mmulL 3 6 A B)) &&
    mmulL 3 6 t c != mmulL 3 6 c t && O.all (fun n => decide (n ≤ 81)) &&
    decide ((O.filter fun n => decide (27 < n)).length ≤ 25)

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
