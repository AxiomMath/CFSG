module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdxDefs
public meta import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBCertInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdxDefs

public section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Kernel
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native

@[expose] def vWords : List (List Nat) := [
    [],[1,1,1,1,1],[1,2,2,2,2],[2,1,1,1,1],[1,1,2,1,2,1],[1,1,2,2,2,1],[1,2,1,1,1,2],
    [1,2,1,2,1,2],[2,1,2,1,2,1],[2,1,2,2,2,1],[2,2,1,1,1,2],[2,2,1,2,1,2],[1,1,1,2,1,2,2],
    [1,2,2,1,2,1,1],[2,1,1,2,1,2,2],[2,2,2,1,2,1,1],[1,1,1,2,2,1,1,2],[1,1,1,2,2,2,1,2],
    [1,1,2,1,1,1,2,2],[1,1,2,2,1,1,2,2],[1,2,1,1,2,2,1,1],[1,2,1,2,2,2,1,1],[1,2,2,1,1,1,2,1],
    [1,2,2,1,1,2,2,1],[2,1,1,2,2,1,1,2],[2,1,1,2,2,2,1,2],[2,1,2,1,1,1,2,2],[2,2,1,1,2,2,1,1],
    [2,2,1,2,2,2,1,1],[2,2,2,1,1,1,2,1],[2,2,2,1,1,2,2,1],[1,1,1,1,2,1,2,2,2],[1,1,1,1,2,2,1,1,1],
    [1,1,2,1,1,2,2,1,2],[1,1,2,2,1,2,2,1,2],[1,2,2,1,2,2,1,2,2],[1,2,2,2,1,1,2,2,2],
    [1,2,2,2,1,2,1,1,1],[2,1,1,1,2,2,1,1,1],[2,1,2,1,1,2,2,1,2],[2,2,1,1,2,1,2,2,1],
    [2,2,1,2,2,1,1,2,1],[2,2,2,1,2,2,1,2,2],[2,2,2,2,1,1,2,2,2],[2,2,2,2,1,2,1,1,1],
    [1,1,1,1,1,1,2,2,2,2],[1,1,1,1,1,2,1,1,1,1],[1,1,1,1,2,1,1,1,1,2],[1,1,1,1,2,1,1,2,1,2],
    [1,1,1,1,2,2,2,1,2,1],[1,1,1,2,1,1,1,1,2,1],[1,1,1,2,1,1,1,2,2,1],[1,1,1,2,2,1,2,2,1,1],
    [1,1,2,1,1,1,1,2,1,1],[1,1,2,1,2,2,1,2,2,2],[1,1,2,1,2,2,2,1,1,1],[1,1,2,2,2,2,1,2,2,2],
    [1,2,1,1,1,1,2,1,1,1],[1,2,1,2,2,2,2,1,2,2],[1,2,2,1,2,2,2,1,1,2],[1,2,2,1,2,2,2,2,1,2],
    [1,2,2,2,1,1,1,2,1,2],[1,2,2,2,1,2,2,1,2,1],[1,2,2,2,1,2,2,2,2,1],[1,2,2,2,2,1,2,2,2,2],
    [2,1,1,1,1,2,1,1,1,1],[2,1,1,1,2,1,1,1,1,2],[2,1,1,2,1,1,1,2,2,1],[2,1,1,2,2,1,2,2,1,1],
    [2,1,2,1,1,1,1,2,1,1],[2,1,2,1,2,2,1,2,2,2],[2,1,2,1,2,2,2,1,1,1],[2,2,1,1,1,1,2,1,1,1],
    [2,2,1,1,2,2,2,1,2,2],[2,2,1,2,1,1,1,2,2,2],[2,2,1,2,2,2,2,1,2,2],[2,2,2,1,2,2,2,1,1,2],
    [2,2,2,2,1,2,2,1,2,1],[2,2,2,2,1,2,2,2,2,1],[1,1,1,1,1,1,1,2,1,2,1],[1,1,1,1,1,1,1,2,2,2,1],
    [1,1,1,1,1,1,2,1,1,1,2],[1,1,1,1,1,1,2,1,2,1,2],[1,1,1,1,1,2,1,2,1,2,1],
    [1,1,1,1,1,2,1,2,2,2,1],[1,1,1,1,1,2,2,1,2,1,2],[1,1,1,1,2,1,2,1,2,1,1],
    [1,1,1,2,1,2,1,2,1,1,1],[1,1,1,2,2,2,2,1,2,2,1],[1,1,2,1,1,2,2,2,2,1,1],
    [1,1,2,1,2,1,2,1,1,1,1],[1,1,2,1,2,2,2,2,1,2,1],[1,1,2,2,1,1,1,1,2,2,1],
    [1,1,2,2,2,1,1,2,2,2,2],[1,1,2,2,2,2,1,1,2,1,2],[1,2,1,1,1,1,2,2,1,2,1],
    [1,2,1,1,1,1,2,2,2,2,1],[1,2,1,1,1,2,2,1,1,1,1],[1,2,1,1,2,1,2,1,1,2,2],
    [1,2,1,1,2,2,2,2,1,1,2],[1,2,1,2,1,1,2,2,1,2,1],[1,2,1,2,1,2,2,1,1,1,1],
    [1,2,1,2,2,1,1,1,1,2,2],[1,2,2,1,1,1,1,2,2,1,2],[1,2,2,1,2,2,1,1,2,1,1],
    [2,1,1,1,1,2,1,2,2,2,1],[2,1,1,1,1,2,2,1,2,1,2],[2,1,1,2,2,2,2,1,1,2,1],
    [2,1,1,2,2,2,2,1,2,2,1],[2,1,2,2,2,1,1,2,2,2,2],[2,2,1,1,1,1,2,2,2,2,1],
    [2,2,1,1,2,1,1,1,1,2,2],[2,2,1,1,2,1,2,1,1,2,2],[2,2,1,2,1,1,2,2,1,2,1],
    [2,2,1,2,2,1,1,1,1,2,2],[1,1,1,1,2,1,1,1,2,2,1,1],[1,1,1,1,2,2,2,1,1,1,2,2],
    [1,1,1,2,1,2,1,2,2,2,2,1],[1,1,1,2,2,2,1,1,1,2,2,2],[1,1,1,2,2,2,1,1,2,1,1,1],
    [1,1,2,1,2,1,2,2,1,1,1,2],[1,1,2,1,2,2,1,2,1,2,1,1],[1,1,2,2,2,1,1,1,2,2,2,1],
    [1,2,1,1,1,2,2,2,1,1,1,2],[1,2,2,1,1,1,2,2,2,1,1,1],[1,2,2,1,2,2,1,1,1,2,2,1],
    [2,1,1,1,2,2,2,1,1,1,2,2],[2,1,2,2,1,1,2,1,2,1,1,1]
  ]

@[expose] def vTbls : Array Table := (vWords.map (wordTbl 315 c2AGens)).toArray

@[expose] def vFind (x : Table) : Nat :=
  ((List.range 128).find? fun k => tblEq 315 x vTbls[k]!).getD 128

@[expose] def vMulTab : Array (Array Nat) :=
  Array.ofFn (n := 128) fun i => Array.ofFn (n := 128) fun j =>
    vFind (compT 315 vTbls[i.val]! vTbls[j.val]!)

@[expose] def vInvTab : Array Nat := Array.ofFn (n := 128) fun i => vFind (invT 315 vTbls[i.val]!)

@[expose] def vT (i j : Nat) : Nat := (vMulTab[i]!)[j]!

@[expose] def vI (i : Nat) : Nat := vInvTab[i]!

@[expose] def u0Tbl : Table := wordTbl 315 crTGens [1, 3]

@[expose] def vCuTab : Array Nat :=
  Array.ofFn (n := 128) fun k => vFind (compT 315 (compT 315 u0Tbl vTbls[k.val]!) (invT 315 u0Tbl))

@[expose] def vCu (k : Nat) : Nat := vCuTab[k]!

@[expose] def vUsq : Nat := vFind (compT 315 u0Tbl u0Tbl)

@[expose] def ivList : List Nat :=
  [0,1,7,8,19,23,24,27,35,47,50,53,57,64,65,75,78,82,83,86,87,90,94,99,102,103,106,107,112,118,
    122,126]

@[expose] def vComm : List Nat :=
  ((List.range 128 ×ˢ List.range 128).map fun p => ci vT vI p.1 p.2).dedup

@[expose] def vBasis : List Nat := [7, 8, 19, 23]

@[expose] def sqPat : Fin 4 → Bool := ![false, false, true, true]

@[expose] def cmPat : Fin 4 → Fin 4 → Bool :=
  ![![false, true, false, true], ![true, false, false, false], ![false, false, false, true],
    ![true, false, true, false]]

@[expose] def ivSq (k : Fin 4) : List Nat :=
  ivList.filter fun i => vT i i == if sqPat k then 1 else 0

@[expose] def vAc (v k : Nat) : Nat := vT (vT v (vCu k)) (vI v)

@[expose] def subIndexCheck : Bool :=
  (List.range 128).all (fun i => vT i (vI i) == 0) &&
  (List.range 128).all (fun i => !((List.range 128).all fun j => vT i j == vT j i) ||
    i == 0 || i == 1) && (List.range 128).all (fun j => vT 1 j == vT j 1) &&
    vComm.all (fun c => vComm.all fun c' => vComm.contains (vT c c')) &&
    (List.range 128).all (fun i => ivList.contains i ==
      vComm.all fun c => ci vT vI i c == 0 || ci vT vI i c == 1) &&
    ivList.all (· < 128) && ivList.Nodup &&
    (List.range 128).all (fun i => !(ivList.all fun l => vT i l == vT l i) || i == 0 || i == 1) &&
    (quads (ivSq 0) (ivSq 1) (ivSq 2) (ivSq 3)).countP (sigIdx vT vI 0 1 sqPat cmPat) == 1920 &&
    ci vT vI 7 8 == 1 &&
    (List.range 128).all fun v =>
      !(vT v (vT (vCu v) vUsq) == 0 && 16 ≤ (List.range 128).countP fun d => vAc v d == d) ||
      (List.range 128).any fun w => vAc v w == vT w 1 && (vT w w == 0 || vT w w == 1) &&
        (List.range 128).all fun d => !(vAc v d == d) || ci vT vI w d == 0 || ci vT vI w d == 1

end CFSG.ComponentClassification.HarrisLit.EndB
