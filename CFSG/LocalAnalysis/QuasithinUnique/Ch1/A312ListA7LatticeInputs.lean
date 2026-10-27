module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven
open Equiv CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def depth : ℕ := 20

@[expose] def dGens : List P7 := [perm7 [[0, 1, 2, 3], [4, 5]], perm7 [[0, 2], [4, 5]]]

@[expose] def elts (G : List P7) : Std.HashSet R7 := bfsSet (G.map R7.enc) depth

@[expose] def latGens : List (List P7) :=
  [dGens,
   dGens ++ [perm7 [[4, 5, 6]]],
   dGens ++ [perm7 [[2, 3], [5, 6]]],
   dGens ++ [perm7 [[2, 3], [4, 5]]],
   dGens ++ [perm7 [[2, 3], [4, 6]]],
   dGens ++ [perm7 [[1, 4], [3, 5]]],
   dGens ++ [perm7 [[2, 3], [4, 5]], perm7 [[2, 3], [5, 6]]],
   dGens ++ [perm7 [[3, 6], [4, 5]]],
   dGens ++ [perm7 [[2, 5], [3, 6]]],
   dGens ++ [perm7 [[2, 4], [3, 6]]],
   dGens ++ [perm7 [[3, 4, 5]]],
   dGens ++ [perm7 [[3, 4], [5, 6]]]]

@[expose] def reps : List P7 :=
  [perm7 [],
   perm7 [[4, 5, 6]],
   perm7 [[3, 4], [5, 6]],
   perm7 [[3, 4, 5]],
   perm7 [[3, 4, 6]],
   perm7 [[3, 6, 4]],
   perm7 [[3, 6], [4, 5]],
   perm7 [[2, 3], [5, 6]],
   perm7 [[2, 3], [4, 5]],
   perm7 [[2, 3], [4, 6]],
   perm7 [[2, 3, 4]],
   perm7 [[2, 3, 4, 5, 6]],
   perm7 [[2, 3, 4, 6, 5]],
   perm7 [[2, 3, 5, 6, 4]],
   perm7 [[2, 3, 5]],
   perm7 [[2, 3, 5, 4, 6]],
   perm7 [[2, 3, 6, 5, 4]],
   perm7 [[2, 3, 6]],
   perm7 [[2, 3, 6, 4, 5]],
   perm7 [[2, 4], [3, 5]],
   perm7 [[2, 4, 3, 5, 6]],
   perm7 [[2, 4, 6, 3, 5]],
   perm7 [[2, 4], [3, 6]],
   perm7 [[2, 4, 3, 6, 5]],
   perm7 [[2, 4, 5, 3, 6]],
   perm7 [[2, 5, 3, 6, 4]],
   perm7 [[2, 5, 4, 3, 6]],
   perm7 [[2, 5], [3, 6]],
   perm7 [[1, 2, 4], [3, 5, 6]],
   perm7 [[1, 2, 4, 3, 5]],
   perm7 [[1, 2, 4, 6], [3, 5]],
   perm7 [[1, 2, 4], [3, 6, 5]],
   perm7 [[1, 2, 4, 3, 6]],
   perm7 [[1, 2, 4, 5], [3, 6]],
   perm7 [[1, 4, 2], [3, 5, 6]],
   perm7 [[1, 4, 3, 5, 2]],
   perm7 [[1, 4, 2], [3, 6, 5]],
   perm7 [[1, 4, 3, 6, 2]],
   perm7 [[1, 4], [3, 5]],
   perm7 [[1, 4, 3, 5, 6]],
   perm7 [[1, 4], [3, 6]],
   perm7 [[1, 4, 3, 6, 5]],
   perm7 [[1, 4], [2, 3, 6, 5]],
   perm7 [[1, 4, 2, 3, 6]],
   perm7 [[1, 4], [2, 5, 3, 6]],
   perm7 [[1, 4, 2, 5], [3, 6]],
   perm7 [[1, 4, 3, 6], [2, 5]],
   perm7 [[1, 4], [2, 6, 3, 5]],
   perm7 [[1, 4, 3, 5], [2, 6]]]

@[expose] def Z (i : ℕ) : Subgroup P7 := Subgroup.closure {g | g ∈ latGens.getD i []}

@[expose] def setEq (a b : Std.HashSet R7) : Bool :=
  decide (a.size = b.size) && a.toList.all (fun x => b.contains x) &&
    b.toList.all (fun x => a.contains x)

@[expose] def eltsLat : List (Std.HashSet R7) := latGens.map elts

@[expose] def isLatCheck (G : List P7) : Bool :=
  let E := elts G
  closedH (G.map R7.enc) E && eltsLat.any fun Z => setEq E Z

@[expose] def dcSet (r : P7) : Std.HashSet R7 :=
  Std.HashSet.ofList ((elts dGens).toList.flatMap fun d =>
    (elts dGens).toList.map fun e => d * R7.enc r * e)

@[expose] def dcSets : List (P7 × Std.HashSet R7) := reps.map fun r => (r, dcSet r)

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven
