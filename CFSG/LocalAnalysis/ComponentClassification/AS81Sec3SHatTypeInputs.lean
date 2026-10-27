module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
public meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests

public section

namespace CFSG.ComponentClassification.AS81.SuzB0

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SuzOddCore

@[expose] def wordTab (w : List Nat) : Array Nat :=
  w.foldl (fun r k => compA 1782 r (cTab k)) (idTab 1782)

@[expose] def commIs (g h c : Array Nat) : Bool :=
  eqA 1782 (compA 1782 g h) (compA 1782 c (compA 1782 h g))

@[expose] def polarBit (v w : Nat) : Nat := (gammaBit v w + gammaBit w v) % 2

@[expose] def typeA0 : Nat := 1

@[expose] def typeYWord : List Nat := [3]

@[expose] def typeY'Word : List Nat := [1, 3, 8, 3, 1]

@[expose] def typeTrans : List (Nat × List Nat) :=
  [(1, []), (2, [9, 2]), (4, [7, 9]), (5, [5, 9]), (6, [2, 1]), (8, [6]), (9, [3, 6]), (10, [9]),
    (15, [7]), (19, [2, 6]), (23, [1, 4]), (27, [4, 4]), (28, [3, 1]), (29, [1]), (30, [7, 2, 1]),
    (35, [7, 2]), (39, [3, 7, 2]), (43, [5, 6]), (44, [4]), (45, [2]), (46, [4, 1]), (51, [6, 1]),
    (55, [9, 1]), (59, [9, 7]), (60, [7, 3, 1]), (61, [2, 9]), (62, [5, 1])]

@[expose] def transOK (w : List Nat) (x : Array Nat) (v : Nat) : Bool :=
  let c := wordTab w
  eqA 1782 (compA 1782 c x) (compA 1782 qProds[v]! c) ||
    eqA 1782 (compA 1782 c x) (compA 1782 (compA 1782 qProds[v]! tTab) c)

@[expose] def commQOK (g : Array Nat) : Bool :=
  allBelow 64 fun u => polarBit u typeA0 == 1 ||
    commIs g qProds[u]! (idTab 1782) || commIs g qProds[u]! qProds[typeA0]!

@[expose] def shatTypeCheck : Bool :=
  let y := wordTab typeYWord
  let y' := wordTab typeY'Word
  let qa := qProds[typeA0]!
  typeA0 != 0 && qMinusBit typeA0 == 0 && typeA0 < 64 &&
  (typeYWord.all fun k => k < 10) && (typeY'Word.all fun k => k < 10) &&
  eqA 1782 (compA 1782 y y) (idTab 1782) && eqA 1782 (compA 1782 y' y') (idTab 1782) &&
  commutesA y qa && commutesA y' qa && commQOK y && commQOK y' &&
  commIs y y' (compA 1782 qa tTab) &&
  (allBelow 64 fun v => v == 0 || qMinusBit v == 1 ||
    match typeTrans.lookup v with
    | some w => (w.all fun k => k < 10) && transOK w qa v
    | none => false)

end CFSG.ComponentClassification.AS81.SuzB0
