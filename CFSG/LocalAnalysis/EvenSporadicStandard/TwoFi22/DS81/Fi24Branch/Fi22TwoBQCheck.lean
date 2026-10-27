module

public import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore

@[expose] def cLine (h : Nat) : Nat := if h < 9 then 19 + h else 79

@[expose] def cBit (i j : Nat) : Bool := i / 2 == j / 2 && i != j

@[expose] def qWords : List (List Int) :=
  [[8, -9, -4, -2, 4, -2, 3, 8, -5, -3, 2, -8, -8, 4],
   [-2, -2, -5, 7, -3, 6, -9, -10, 2, -4, 9, 8, 5, 6, 2, -1, 3, -7, -2, -2, -7, -3, 9, 4, 4, 8,
    2, -5, 8],
   [7, 2, 2, 2, -6, -4, -3, 7, 1, 8, 1, -2, 8, 10, 9, 3, -2, -7, 2, -3, -4, 9, 8, 5, 6, 2],
   [-2, -2, -7, -5, -3, 6, 4, 9, 2, 3, -2, -7, 2, -3, -3, 2, -8, -8, 4],
   [3, -5, 1, 2, -7, -2, -2, -7, 2, -3, -3, 2, -8, -8, 4],
   [-10, 6, -4, 1, -2, 3, 10, -6, 10, 3, -2, -7, 2, -3, 9, 4, 4, 8, 2, -5, 8],
   [7, 2, 2, 2, -6, -4, -3, 7, 1, 9, 4, 4, 8, 2, -5, 8],
   [3, 3, -4, 2, -5, -10, -10, 7, 1, 8, 1, -2, 8, 10, 9, -7, 9, 7, 9, -1, 3, -7, -2, -2, -7, -3],
   [8, 8, -3, -4, 9, 7, 3, 5, 2, 3, -2, -7, 2, -3, -3, 2, -8, -8, 4],
   [-5, -6, -10, -10, -4, 9, -8, 3, 2, 8, 1, -2, 8, 10, 9, 3, -2, -7, 2, -3]]

@[expose] def actCodes : List Nat :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 711, 128, 134, 316, 516, 521, 779, 1552, 941, 150, 2009,
   2046, 1298, 461, 59, 1660, 1170, 1129, 2020, 1784, 1041, 1836, 1424, 657, 148, 2005, 1868,
   1044, 1025, 1578, 1, 1026, 1028, 8, 80, 1120, 64, 944, 320, 1600, 169, 1342, 1879, 265, 1859,
   393, 1554, 40, 424, 573, 1193, 426, 179, 416, 15, 392, 351, 128, 256, 1685, 1316, 1459, 1774,
   977, 505, 2005, 34, 818, 631, 1939, 1190, 1015, 572, 739, 1973, 1637, 106, 548, 195, 1931,
   1429, 1976, 1682, 494, 816, 791, 1688, 964, 138, 199]

@[expose] def genArr (h : Nat) : Array Nat := fi22CentArr (cLine h)

@[expose] def t1Arr : Array Nat := fi22ExtArr (21 + 1)

@[expose] def tPowA (t : Array Nat) (b : Bool) : Array Nat := if b then t else idA 3510

@[expose] def prodA : List (Array Nat) → Array Nat
  | [] => idA 3510
  | a :: l => compA 3510 a (prodA l)

@[expose] def monA (qa : Array (Array Nat)) (v : Nat) : Array Nat :=
  prodA (List.ofFn fun i : Fin 10 => if v.testBit i then qa[(i : Nat)]! else idA 3510)

@[expose] def nfA (t : Array Nat) (qa : Array (Array Nat)) (code : Nat) : Array Nat :=
  compA 3510 (tPowA t (code.testBit 10)) (monA qa code)

@[expose] def qWordsOK : Bool := qWords.length == 10 && qWords.all (lettersOK 10)

@[expose] def relOK (t : Array Nat) (qa : Array (Array Nat)) : Bool :=
  let one := idA 3510
  eqA 3510 (compA 3510 t t) one && !eqA 3510 t one &&
    (List.range 10).all fun j =>
      eqA 3510 (compA 3510 t qa[j]!) (compA 3510 qa[j]! t) &&
        eqA 3510 (compA 3510 qa[j]! qa[j]!) one

@[expose] def commOK (t : Array Nat) (qa : Array (Array Nat)) : Bool :=
  (List.range 10).all fun i => (List.range 10).all fun j =>
    eqA 3510 (compA 3510 qa[i]! qa[j]!) (compA 3510 (compA 3510 qa[j]! qa[i]!) (tPowA t (cBit i j)))

@[expose] def conjOK (S Si : Array (Array Nat)) (t : Array Nat) (qa : Array (Array Nat)) : Bool :=
  (List.range 10).all fun k => (List.range 10).all fun j =>
    eqA 3510 (compA 3510 (compA 3510 S[k]! qa[j]!) Si[k]!)
      (nfA t qa (actCodes.getD (10 * k + j) 0))

@[expose] def centOK (S : Array (Array Nat)) (t : Array Nat) : Bool :=
  (List.range 10).all fun k => eqA 3510 (compA 3510 S[k]! t) (compA 3510 t S[k]!)

@[expose] def checkQ (_ : Unit := ()) : Bool :=
  let S : Array (Array Nat) := Array.ofFn (n := 10) fun h => genArr h
  let Si : Array (Array Nat) := S.map (invCand 3510)
  let t : Array Nat := t1Arr
  let qa : Array (Array Nat) := Array.ofFn (n := 10) fun j => wordA 3510 S Si (qWords.getD j [])
  qWordsOK && relOK t qa && commOK t qa && conjOK S Si t qa && centOK S t

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
