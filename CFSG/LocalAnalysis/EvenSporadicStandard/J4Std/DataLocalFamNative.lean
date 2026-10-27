module

public import CFSG.Sporadic.J4.QTRankNative
public import Std.Data.HashSet.Basic

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataLocal

open CFSG.Sporadic.J4.QT

@[expose] def invs : List (List Nat) :=
  tabL.filter fun t => compT t t == idT && t != idT

@[expose] def nInv : Nat := invs.length

@[expose] def inv (i : Nat) : List Nat := invs.getD i []

@[expose] def commutes (i j : Nat) : Bool :=
  compT (inv i) (inv j) == compT (inv j) (inv i)

@[expose] def maskOf (l : List Nat) : Nat := l.foldl (fun acc j => acc ||| (1 <<< j)) 0

@[expose] def commMasks : List Nat :=
  (List.range nInv).map fun i => maskOf ((List.range nInv).filter fun j => commutes i j)

@[expose] def prodTab : List (List Nat) :=
  (List.range nInv).map fun i => (List.range nInv).map fun j =>
    if commutes i j then invs.idxOf (compT (inv i) (inv j)) else 0

@[expose] def prodIdx (i j : Nat) : Nat := (prodTab.getD i []).getD j 0

@[expose] def bitIdx (m : Nat) : List Nat := (List.range nInv).filter fun j => m.testBit j

@[expose] def extWith (bs : List Nat) (m i : Nat) : Nat :=
  m ||| maskOf (i :: bs.map fun j => prodIdx i j)

@[expose] def ext (m i : Nat) : Nat := extWith (bitIdx m) m i

@[expose] def cands (m : Nat) : List Nat :=
  (List.range nInv).filter fun i => !m.testBit i && (m &&& commMasks.getD i 0 == m)

@[expose] def exts (m : Nat) : List Nat :=
  let bs := bitIdx m
  (cands m).map (extWith bs m)

@[expose] def dedup (l : List Nat) : List Nat :=
  (l.foldl (fun (s : Std.HashSet Nat) x => s.insert x) {}).toList

@[expose] def next (F : List Nat) : List Nat := dedup (F.flatMap exts)

@[expose] def levelsFrom : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | k + 1, F => F :: levelsFrom k (next F)

@[expose] def levels : List (List Nat) := levelsFrom 8 [0]

@[expose] def fixList (i : Nat) : List Nat := (List.range 2048).filter fun c => actT (inv i) c == c

@[expose] def fixLists : List (List Nat) := (List.range nInv).map fixList

@[expose] def fixCntFrom : List Nat → Nat
  | [] => 2048
  | i :: bs => ((fixLists.getD i []).filter fun c => bs.all fun j => actT (inv j) c == c).length

@[expose] def fixCnt (m : Nat) : Nat := fixCntFrom (bitIdx m)

@[expose] def boundOK (m : Nat) : Bool :=
  m == 0 || fixCnt m * ((bitIdx m).length + 1) ≤ 1024

@[expose] def chkTabs : Bool :=
  (List.range nInv).all fun i => (List.range nInv).all fun j =>
    ((commMasks.getD i 0).testBit j == commutes i j) &&
      (i == j || !commutes i j ||
        (prodIdx i j < nInv && inv (prodIdx i j) == compT (inv i) (inv j)))

@[expose] def chkFam : Bool :=
  chkTabs && (levels.getD 7 []).isEmpty &&
    levels.all fun L => L.all fun m => m >>> nInv == 0 && boundOK m

end CFSG.EvenSporadicStandard.J4Std.DataLocal
