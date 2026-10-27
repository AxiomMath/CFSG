module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabWitData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

@[expose] def translA (v : ℕ) : Array ℕ := Array.ofFn fun x : Fin 64 => x.val ^^^ v

@[expose] def linV (imgs : List ℕ) (v : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc i => if v.testBit i then acc ^^^ imgs[i]! else acc) 0

@[expose] def linA (imgs : List ℕ) : Array ℕ := Array.ofFn fun x : Fin 64 => linV imgs x.val

@[expose] def injA (t : Array ℕ) : Bool :=
  (List.range 64).all fun x => (List.range 64).all fun y => x == y || t[x]! != t[y]!

@[expose] def ovalPresA (t : Array ℕ) : Bool :=
  hexaOval.all fun L => hexaOval.any fun L' => L.all fun x => L'.contains t[x]!

@[expose] def ovalPairs : List (ℕ × ℕ) :=
  hexaOval.flatMap fun L => (L.filter (· != 0)).flatMap fun a =>
    ((L.filter (· != 0)).filter (· != a)).map fun b => (a, b)

@[expose] def stabCands : List (Array ℕ) :=
  ovalPairs.flatMap fun p => ovalPairs.flatMap fun q => ovalPairs.map fun r =>
    linA [p.1, p.2, q.1, q.2, r.1, r.2]

@[expose] def stabIdx (W : List ℕ) (c : ℕ) : ℕ := (W[c / 648]! >>> (12 * (c % 648))) % 4096

@[expose] def stabW (M : List (Array ℕ)) (W : List ℕ) : Bool :=
  (List.range stabCands.length).all fun c =>
    !(ovalPresA stabCands[c]! && injA stabCands[c]!) ||
      (decide (stabIdx W c < M.length) && eqA 64 stabCands[c]! M[stabIdx W c]!)

@[expose] def spanL (L L' : List ℕ) : List ℕ := L.flatMap fun x => L'.map fun y => x ^^^ y

@[expose] def framePairs : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

@[expose] def offFrame (x : ℕ) : Bool :=
  framePairs.all fun p => !((spanL hexaOval[p.1]! hexaOval[p.2]!).contains x)

@[expose] def ovalCompN : Bool :=
  (List.range 64).all fun a => (List.range 64).all fun b =>
    !(a != 0 && b != 0 && a != b && offFrame a && offFrame b && offFrame (a ^^^ b)) ||
      (hexaOval[4]!.contains a && hexaOval[4]!.contains b) ||
      (hexaOval[5]!.contains a && hexaOval[5]!.contains b)

@[expose] def hexaStabCheck : Bool :=
  let M := eltsN 64 hexaMGens
  hexaTGens == (List.range 6).map (fun i => translA (2 ^ i)) &&
    hexaR0Gens == [translA 1, translA 2] && stabW M hexaStabW &&
    enumCheckN 64 hexaM2Gens 2160 && hexaM2Gens.all (inLN 64 M) &&
    hexaM2Gens.all (fun a => eqA 64 (powN 64 a 4) (idA 64)) && ovalCompN

end CFSG.ComponentClassification.AS81.Hexa
