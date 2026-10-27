module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshPresModel
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshQData

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open CFSG.EvenSporadicStandard.Fin76b

@[expose] def swN (l : List ℤ) : List (Fin 9 × Bool) :=
  l.map fun z => (Fin.ofNat 9 (z.natAbs - 1), decide (0 < z))

@[expose] def invL (l : List ℤ) : List ℤ := l.reverse.map fun z => -z

@[expose] def commL (a b : List ℤ) : List ℤ := invL a ++ invL b ++ a ++ b

@[expose] def cL : List ℤ := [1, 1]

@[expose] def Wx (α β : ℕ) : List (List ℤ) :=
  if α = 0 then
    (if β = 0 then [[1], [2, 5], [3], [4, 5], [5], [1, 3, 6]]
      else [[1], [1, 2, 3, 5, 6], [3], [1, 3, 4, 5, 6], [1, 3, 5, 1, 1], [1, 3, 6]])
  else
    (if β = 0 then [[3, 1, 1], [4, 5, 1, 1], [1, 1, 1], [2, 5], [5, 1, 1], [1, 3, 6, 1, 1]]
      else [[3, 1, 1], [1, 3, 4, 5, 6, 1, 1], [1, 1, 1], [1, 2, 3, 5, 6], [1, 3, 5, 1, 1],
        [1, 3, 6, 1, 1]])

@[expose] def Wt (α : ℕ) : List (List ℤ) :=
  if α = 0 then [[1, 1, 1], [1, 2, 1, 1], [3, 1, 1], [3, 4, 1, 1], [5], [6]]
  else [[1, 1, 1], [1, 2, 1, 1], [3, 1, 1], [3, 4, 1, 1], [5, 1, 1], [6]]

@[expose] def Ws : List (List ℤ) := [[2], [1, 2], [4], [3, 4], [5], [6]]

@[expose] def actRel (z : ℤ) (W : List (List ℤ)) : List (List ℤ) :=
  (List.range 6).map fun i => [-z, ((i + 1 : ℕ) : ℤ), z] ++ invL (W.getD i [])

@[expose] def relEL : List (List ℤ) :=
  [[6, 6], [5, 5], [1, 1, 1, 1], [2, 2] ++ invL cL, [3, 3] ++ invL cL, [4, 4] ++ invL cL,
   commL [1] [2] ++ invL cL, commL [3] [4] ++ invL cL, commL [5] [6] ++ invL cL,
   commL cL [2], commL cL [3], commL cL [4], commL cL [5], commL cL [6],
   commL [1] [3], commL [1] [4], commL [2] [3], commL [2] [4], commL [1] [5], commL [1] [6],
   commL [2] [5], commL [2] [6], commL [3] [5], commL [3] [6], commL [4] [5], commL [4] [6]]

@[expose] def relNQL (α β : ℕ) : List (List ℤ) :=
  relEL ++ actRel 9 (Wt α) ++ [[9, 9]] ++ actRel 7 (Wx α β) ++ [[7, 7], commL [7] [9]]

@[expose] def relNSL (k : ℕ) : List (List ℤ) :=
  actRel 8 Ws ++
    [[8, 8, 8], [8, 9, 8, 9], [8, 7, 8, 7, 8, 7] ++ (List.replicate k (invL cL)).flatten]

@[expose] def relN (α β k : ℕ) : List (List (Fin 9 × Bool)) :=
  (relNQL α β ++ relNSL k).map swN


@[expose] def nBase0 : Array Table :=
  #[#[2,0,6,7,8,10,1,4,3,5,13,14,15,9,12,11],
  #[4,8,7,0,6,12,3,1,2,15,14,5,13,11,9,10],
  #[1,6,0,7,8,9,2,4,3,13,5,14,15,10,12,11],
  #[3,8,7,6,0,11,4,1,2,15,14,13,5,12,9,10],
  #[0,1,2,3,4,13,6,7,8,10,9,12,11,5,15,14],
  #[5,9,10,11,12,0,13,14,15,1,2,3,4,6,7,8],
  #[0,1,2,3,4,5,6,7,8,9,10,12,11,13,15,14],
  #[0,7,8,1,2,5,6,3,4,14,15,9,10,13,11,12],
  #[6,1,2,7,8,13,0,3,4,9,10,14,15,5,11,12]]

@[expose] def nBase1 : Array Table :=
  #[#[5,4,15,14,0,1,10,11,12,13,7,6,9,8,2,3],
  #[3,2,0,1,14,15,8,9,7,6,13,12,10,11,5,4],
  #[5,4,14,15,0,1,11,10,12,13,6,7,9,8,3,2],
  #[3,2,0,1,15,14,9,8,6,7,13,12,10,11,4,5],
  #[12,13,11,10,8,9,15,14,4,5,3,2,0,1,7,6],
  #[1,0,3,2,5,4,6,7,8,9,10,11,12,13,15,14],
  #[4,5,7,6,0,1,3,2,12,13,14,15,8,9,10,11],
  #[4,5,1,0,3,2,6,7,10,11,12,13,8,9,14,15],
  #[4,5,2,3,0,1,6,7,13,12,11,10,9,8,15,14]]


@[expose] def nGens (α k : ℕ) : Array Table :=
  let b := if α = 0 then nBase0 else nBase1
  b.set! 6 (compT 16 b[6]! (powT 16 k (compT 16 b[0]! b[0]!)))

@[expose] def nCheck (α k : ℕ) : Bool :=
  modelCheck 16 16 9 (nGens α k) (relN α α k) 3072

@[expose] def toQ (α β : ℕ) (i : Fin 9) : List (Fin 8 × Bool) :=
  match i with
  | 0 => [(1, true), (2, true)]
  | 1 => [(1, true), (1, true), (3, true), (5, true)]
  | 2 => [(1, true), (2, false)]
  | 3 => [(1, false), (2, false), (5, true)]
  | 4 => [(6, true)]
  | 5 => [(0, true)]
  | 6 => [(7, true)] ++ powW ([(1, true), (1, true), (2, true), (3, true)] ++
      [(1, true), (2, true)] ++ [(1, true), (1, true), (3, true), (5, true)] ++
      [(1, false), (2, false), (5, true)] ++ [(6, true)] ++ powW [(0, true)] β) α
  | 7 => []
  | 8 => [(1, true), (1, true), (2, true), (3, true)]

@[expose] def relNQCheck (α β : ℕ) : Bool :=
  wordsTrivial 24 (fun i : Fin 8 => (qGens α β)[i.val]!) (fun i : Fin 8 => (qInvs α β)[i.val]!)
    ((relNQL α β).map fun r => substW (toQ α β) (swN r))

end CFSG.EvenSporadicStandard.M12Std.Yosh
