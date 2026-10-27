module

public import Certificates.Data.SmithECheck
public import Certificates.Data.SMod20BasicData

public section

namespace CFSG.SmithE

open CFSG.F4.Native

@[expose] def ptImg (j a : Nat) : Nat := uPos[normC (tvC uPts[j]! uPts[a]!)]!

@[expose] def ptTab : Array (Array Nat) :=
  Array.ofFn (n := 693) fun j => Array.ofFn (n := 693) fun a => ptImg j.val a.val

@[expose] def wordImg (w : List Nat) (a : Nat) : Nat := w.foldl (fun b j => ptImg j b) a

@[expose] def inPlane (i a : Nat) : Bool := (maskArr[i]!).testBit uPts[a]!

@[expose] def planePts (i : Nat) : Array Nat := ((List.range 693).filter (inPlane i)).toArray

@[expose] def planePtsArr : Array (Array Nat) := Array.ofFn (n := 891) fun i => planePts i.val

@[expose] def planeImg (k i : Nat) : Nat := wtIdx[applyCols tvArr[k]! wtArr[i]!]!

@[expose] def planeWordImg (w : List Nat) (i : Nat) : Nat := w.foldl (fun b k => planeImg k b) i

@[expose] def oppB (i j : Nat) : Bool := planePtsArr[i]!.all fun a => !inPlane j a

@[expose] def fB (u v : Nat) : Bool :=
  (List.range 10).foldl (fun acc k => acc ^^
    ((u.testBit (2 * k) && v.testBit (2 * k + 1)) ^^ (u.testBit (2 * k + 1) && v.testBit (2 * k))))
    false

@[expose] def chkTvInv : Bool :=
  (List.range 693).all fun k => let T := tvArr[k]!
    T.size == 20 &&
      (List.range 20).all fun m => decide (T[m]! < 2 ^ 20) && applyCols T T[m]! == 2 ^ m

@[expose] def chkTvConj : Bool :=
  (List.range 693).all fun j => let Tj := tvArr[j]!
    (List.range 693).all fun a => let b := ptImg j a
      decide (b < 693) && (let Ta := tvArr[a]!; let Tb := tvArr[b]!
        (List.range 20).all fun m => applyCols Tj (applyCols Ta Tj[m]!) == Tb[m]!)

@[expose] def chkPtWords : Bool :=
  (List.range 693).all fun a =>
    ptWords[a]!.all (fun j => decide (j < 693)) && wordImg ptWords[a]! a == 0

@[expose] def chkPairWords : Bool :=
  (List.range 693).all fun l => hermC uPts[0]! uPts[l]! == 0 ||
    (pairWords[l]!.all (fun j => decide (j < 693) && ptImg j 0 == 0) &&
      wordImg pairWords[l]! l == 1)

@[expose] def chkPlaneWords : Bool :=
  (List.range 891).all fun i =>
    planeWords[i]!.all (fun k => decide (k < 693)) && planeWordImg planeWords[i]! i == 0

@[expose] def chkTW : Bool :=
  (List.range 693).all fun k => let T := tvArr[k]!; let P := ptTab[k]!
    (List.range 891).all fun i => let j := planeImg k i
      decide (j < 891) && wtArr[j]! == applyCols T wtArr[i]! &&
        planePtsArr[i]!.all fun a => inPlane j P[a]!

@[expose] def chkPlanes : Bool :=
  (List.range 891).all (fun i => planePtsArr[i]!.size == 21) &&
    (List.range 891).all fun i => (List.range i).all fun j => planePtsArr[i]! != planePtsArr[j]!

@[expose] def chkGram : Bool :=
  (List.range 891).all fun i => (List.range 891).all fun j => fB wtArr[i]! wtArr[j]! == oppB i j

@[expose] def chkFormInv : Bool :=
  (List.range 693).all fun k => let T := tvArr[k]!
    (List.range 20).all fun a => (List.range 20).all fun b => fB T[a]! T[b]! == fB (2 ^ a) (2 ^ b)

end CFSG.SmithE
