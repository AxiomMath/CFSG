module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Code

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def frobStable (L : Array (Array ℕ)) : Bool :=
  (List.range L.size).all fun n => L.contains (frobCode L[n]!)

@[expose] def semiComm (a b : Array ℕ × ℕ) : Bool := semi a b == semi b a

@[expose] def centerOK (L : Array (Array ℕ)) (gens : List (Array ℕ × ℕ)) (zc : Array ℕ) : Bool :=
  (List.range 243).all fun n => (List.range 3).all fun s =>
    !(gens.all fun g => semiComm (L[n]!, s) g) ||
      (s == 0 && (L[n]! == idCode || L[n]! == zc || L[n]! == mulCode zc zc))

@[expose] def aList (U Z : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 81) fun t => mulCode (powCode U (t.val / 9)) (powCode Z (t.val % 9))

@[expose] def aOK (L : Array (Array ℕ)) (U Z : Array ℕ) : Bool :=
  let A := aList U Z
  A[0]! == idCode &&
  (List.range 81).all (fun i => (List.range 81).all fun j => A.contains (mulCode A[i]! A[j]!)) &&
  (List.range 81).all (fun i => (List.range 81).any fun j => mulCode A[i]! A[j]! == idCode) &&
  (List.range 81).all (fun i => (List.range i).all fun j => A[i]! != A[j]!) &&
  (List.range 81).all (fun i => L.contains A[i]!)

@[expose] def omegaOK (U Z : Array ℕ) : Bool :=
  let A := aList U Z
  (List.range 81).all fun t => powCode A[t]! 3 != idCode || (t / 9 % 3 == 0 && t % 9 % 3 == 0)

@[expose] def compOK (L : Array (Array ℕ)) (U Z : Array ℕ) : Bool :=
  let A := aList U Z
  let a0 := powCode U 3
  let b0 := powCode Z 3
  (List.range 243).all fun n =>
    A.contains L[n]! || powCode L[n]! 3 != idCode || mulCode L[n]! a0 != mulCode a0 L[n]! ||
      mulCode L[n]! b0 != mulCode b0 L[n]!

@[expose] def qOK (L : Array (Array ℕ)) (zc : Array ℕ) (bi yi : ℕ) : Bool :=
  bi < 243 && yi < 243 &&
  L[bi]! != idCode && L[bi]! != zc && L[bi]! != mulCode zc zc && powCode L[bi]! 3 == idCode &&
  mulCode zc L[bi]! == mulCode L[bi]! zc &&
  semi (L[yi]!, 1) (semi (L[yi]!, 1) (L[yi]!, 1)) == semiOne &&
  semiComm (L[yi]!, 1) (zc, 0) && semiComm (L[yi]!, 1) (L[bi]!, 0)

@[expose] def qList (zc b : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 9) fun t => mulCode (powCode zc (t.val / 3)) (powCode b (t.val % 3))

@[expose] def gOK (zc b1 b2 : Array ℕ) (gw : List (List ℕ)) : Bool :=
  gw.length == 4 && (List.range 4).all fun j =>
    mulCode (wordCode gw[j]!) (wordCode (gw[j]!).reverse) == idCode &&
    mulCode (wordCode (gw[j]!).reverse) (wordCode gw[j]!) == idCode &&
    (mulCode (mulCode (wordCode gw[j]!) zc) (wordCode (gw[j]!).reverse) == zc ||
      mulCode (mulCode (wordCode gw[j]!) zc) (wordCode (gw[j]!).reverse) == mulCode zc zc) &&
    (qList zc (if j < 2 then b1 else b2)).contains
      (mulCode (mulCode (wordCode gw[j]!) (if j < 2 then b1 else b2))
        (wordCode (gw[j]!).reverse))

@[expose] def zOKc (L : Array (Array ℕ)) (zc : Array ℕ) (gens : List (Array ℕ × ℕ)) : Bool :=
  zc != idCode && powCode zc 3 == idCode && frobCode zc == zc && L[81]! == zc &&
    gens.all fun g => semiComm (zc, 0) g

end CFSG.AGLEmbedding.KFactProofs.G28
