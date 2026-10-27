module

public import Certificates.Data.CFSGNative.Fi23.Slp
public import CFSG.Perm.ChainByOrder
public import CFSG.Sporadic.Co2Cert.Data

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

@[expose] def co2T (k : Nat) : Table := (CFSG.Sporadic.Co2Cert.co2OrigArrs[k]!).map UInt32.ofNat

@[expose] def co2Gens (T0 T1 : Table) (z : Int) : Table :=
  if z = 1 then T0 else if z = -1 then invT 2300 T0 else if z = 2 then T1 else invT 2300 T1

@[expose] def parseInt (t : String) : Int :=
  if t.startsWith "-" then -Int.ofNat (t.drop 1).toNat! else Int.ofNat t.toNat!

@[expose] def parseIntLists (s : String) : Array (List Int) :=
  (s.splitOn ";").toArray.map fun t => if t.isEmpty then [] else (t.splitOn ",").map parseInt

@[expose] def subLetters (L : Array Table) (ws : Array Nat) : Array Table :=
  Array.ofFn (n := 2 * ws.size) fun i =>
    if i.val % 2 = 0 then L[2 * ws[i.val / 2]!]! else L[2 * ws[i.val / 2]! + 1]!

@[expose] def eqTab2 (A B : Table) : Bool := (List.range 2300).all fun i => ap A i == ap B i

@[expose] def cardCo2 (_ : Unit := ()) : Nat := 42305421312000

structure Co2SevenData where
  words : Array (List Int)
  is : Nat
  ih : Nat
  id : Array Nat
  chain : Array Nat

@[expose] def centTabs7 (n : Nat) (Y : Table) (Ds : Array Table) : Array Table :=
  (Array.range 56).map fun t => compT n (powT n (t / 8) Y) Ds[t % 8]!

@[expose] def imagesDistinct (T : Array Table) (ω : Nat) : Bool :=
  (List.range T.size).all fun s => (List.range T.size).all fun t =>
    s == t || ap T[s]! ω != ap T[t]! ω

@[expose] def co2SevenOK (D : Co2SevenData) (m bound : Nat) : Bool :=
  let n := 2300
  let T0 := co2T 0
  let T1 := co2T 1
  let L := slpLetters n (co2Gens T0 T1) D.words
  let Y := L[2 * D.is]!
  let ω := ap L[2 * D.ih]! 0
  let Ds := D.id.map fun j => L[2 * j]!
  let base := (Array.range m).map fun i => iterAp Y i ω
  let LC := subLetters L D.chain
  let trees := chainTrees n LC base
  let T := centTabs7 n Y Ds
  invOK n T0 (invT n T0) && invOK n T1 (invT n T1) && slpOK D.words &&
    decide (D.is < D.words.size) && decide (D.ih < D.words.size) &&
    decide (D.id.size = 8) && D.id.all (fun j => decide (j < D.words.size)) &&
    (List.range D.words.size).all (fun j => invOK n L[2 * j]! L[2 * j + 1]!) &&
    D.chain.all (fun j => decide (j < D.words.size)) && decide (ω < n) && decide (0 < m) &&
    eqTab2 (powT n 7 Y) (idT n) && !(eqTab2 Y (idT n)) &&
    Ds.all (fun E => eqTab2 (compT n E Y) (compT n Y E)) &&
    (List.range m).all (fun i => treeOK n base[i]! trees[i]! LC (levelLetters LC base i)) &&
    decide ((List.range m).foldl (fun acc i => acc * trees[i]!.pts.size) 1 = cardCo2 ()) &&
    decide (Nat.count (fun p => sift trees LC (Array.range m) base 0 (tupleOf Y m p) = true) n ≤
      bound) &&
    imagesDistinct T ω

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative
