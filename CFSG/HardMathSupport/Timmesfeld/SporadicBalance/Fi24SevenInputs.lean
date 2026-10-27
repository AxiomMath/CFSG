module

public import Certificates.Data.CFSGNative.Fi24.Certificate
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CoreByTree
public meta import Certificates.Data.CFSGNative.Fi24.Certificate
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CoreByTree
public import CFSG.Foundations.Basic
public meta import CFSG.Foundations.Basic
public import CFSG.Perm.ChainByOrder
public meta import CFSG.Perm.ChainByOrder

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

structure RepData where
  rep : Nat
  chain : Array Nat
  cent : Array Nat
  omega : List Nat
  e : Nat
  m : Nat
  wit : Array (List Nat)

structure Data where
  words : Array (List Int)
  ix : Nat
  iy : Nat
  ic : Nat
  conj : Array (Nat × List Nat)
  repA : RepData
  repB : RepData

@[expose] def parseLists (s : String) : Array (List Nat) :=
  (s.splitOn ";").toArray.map fun t => if t.isEmpty then [] else (t.splitOn ",").map String.toNat!

@[expose] def parseInt (t : String) : Int :=
  if t.startsWith "-" then -Int.ofNat (t.drop 1).toNat! else Int.ofNat t.toNat!

@[expose] def parseIntLists (s : String) : Array (List Int) :=
  (s.splitOn ";").toArray.map fun t => if t.isEmpty then [] else (t.splitOn ",").map parseInt

@[expose] def parsePairs (s : String) : Array (Nat × List Nat) :=
  (s.splitOn ";").toArray.map fun t =>
    match t.splitOn "|" with
    | [a, b] => (a.toNat!, if b.isEmpty then [] else (b.splitOn ",").map String.toNat!)
    | _ => (0, [])

@[expose] def subLetters (L : Array Table) (ws : Array Nat) : Array Table :=
  Array.ofFn (n := 2 * ws.size) fun i =>
    if i.val % 2 = 0 then L[2 * ws[i.val / 2]!]! else L[2 * ws[i.val / 2]! + 1]!

@[expose] def wordApply (L : Array Table) (w : List Nat) (q : Array Nat) : Array Nat :=
  w.foldr (fun l q => apT L[l]! q) q

@[expose] def powApplyT (t : Table) : Nat → Array Nat → Array Nat
  | 0, q => q
  | e + 1, q => apT t (powApplyT t e q)

@[expose] def cubeApply (X Y C : Table) (i j k : Nat) (q : Array Nat) : Array Nat :=
  powApplyT X i (powApplyT Y j (powApplyT C k q))

@[expose] def eqTab7 (A B : Table) : Bool := (List.range 306936).all fun i => ap A i == ap B i

@[expose] def basePts : Array Nat := chainBase

@[expose] def cubeOK7 (X Y C : Table) : Bool :=
  let I := idT 306936
  eqTab7 (powT 306936 7 X) I && eqTab7 (powT 306936 7 Y) I &&
    eqTab7 C (compT 306936 X (compT 306936 Y (compT 306936 (powT 306936 6 X) (powT 306936 6 Y)))) &&
    eqTab7 (compT 306936 C X) (compT 306936 X C) && eqTab7 (compT 306936 C Y) (compT 306936 Y C) &&
    let imgs := (List.range 343).map fun t => cubeApply X Y C (t / 49) (t / 7 % 7) (t % 7) basePts
    (List.range 343).all fun s => (List.range s).all fun t => !tupleEq imgs[s]! imgs[t]!

@[expose] def conjOK7 (L : Array Table) (X Y C : Table) (conj : Array (Nat × List Nat)) : Bool :=
  (List.range 343).all fun t => t == 0 ||
    let e := conj[t]!
    let R := if e.1 == 0 then Y else C
    e.2.all (fun l => decide (l < L.size)) &&
      tupleEq (wordApply L e.2 (cubeApply X Y C (t / 49) (t / 7 % 7) (t % 7) basePts))
        (apT R (wordApply L e.2 basePts))

@[expose] def cardJ (_ : Unit := ()) : Nat := 1255205709190661721292800

@[expose] def repOK (L : Array Table) (R : Table) (D : RepData) : Bool :=
  let LC := subLetters L D.chain
  let ω := (wordApply L D.omega #[0])[0]!
  let base := (Array.range 7).map fun i => iterAp R i ω
  let trees := chainTrees 306936 LC base
  let LZ := subLetters L D.cent
  let lvZ := (Array.range D.cent.size).map fun j => 2 * j
  let T := treeBFS 306936 ω LZ lvZ
  D.omega.all (fun l => decide (l < L.size)) && D.chain.all (fun j => decide (2 * j + 1 < L.size)) &&
    D.cent.all (fun j => decide (2 * j + 1 < L.size)) && decide (ω < 306936) &&
    (List.range 7).all (fun i => treeOK 306936 base[i]! trees[i]! LC (levelLetters LC base i)) &&
    decide ((List.range 7).foldl (fun acc i => acc * trees[i]!.pts.size) 1 = cardJ ()) &&
    treeOK 306936 ω T LZ lvZ &&
    lvZ.all (fun l => eqTab7 (compT 306936 LZ[l]! R) (compT 306936 R LZ[l]!)) &&
    decide (Nat.count (fun p => sift trees LC (Array.range 7) base 0 (tupleOf R 7 p) = true)
      306936 ≤ T.pts.size) &&
    decide (T.pts.size = 7 ^ D.e * D.m) && decide (D.wit.size = T.pts.size) &&
    (List.range T.pts.size).all (fun k => (D.wit[k]!).all fun j => decide (j < T.pts.size)) &&
    (List.range T.pts.size).all fun k => k == 0 || witOK T LZ k D.wit[k]! D.m basePts

@[expose] def fi24SevenOK (D : Data) (O : Enum) : Bool :=
  let L := slpLetters 306936 (genTables O) D.words
  let X := L[2 * D.ix]!
  let Y := L[2 * D.iy]!
  let C := L[2 * D.ic]!
  slpOK D.words && decide (2 * D.ix < L.size) && decide (2 * D.iy < L.size) &&
    decide (2 * D.ic < L.size) &&
    (List.range D.words.size).all (fun j => invOK 306936 L[2 * j]! L[2 * j + 1]!) &&
    decide (D.conj.size = 343) && cubeOK7 X Y C && conjOK7 L X Y C D.conj &&
    D.repA.rep == D.iy && D.repB.rep == D.ic && repOK L Y D.repA && repOK L C D.repB

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
