module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.BCheck
public import Certificates.Data.CFSGNative.MonsterB.BinaryRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.SectionRank.Native CFSG.Blueprint CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

set_option compiler.extract_closed false

@[expose] def bG (k : Nat) : Nat := [81, 60].getD k 0

@[expose] def bGInv (k : Nat) : Nat := [83, 84].getD k 0

@[expose] def nfXData : List (List Nat) :=
  [[2, 2, 2, 2, 0, 0, 2, 2, 2], [2, 0, 2, 0, 2, 2, 2, 2, 2], [0, 1, 0, 1, 2, 1, 0, 1, 2],
   [2, 2, 1, 2, 1, 1, 0, 1, 0],
   [1, 1, 0, 2, 0, 0, 2, 0, 0], [2, 0, 2, 2, 1, 2, 0, 2, 0], [1, 1, 1, 0, 0, 2, 0, 0, 0],
   [1, 0, 1, 0, 1, 2, 0, 1, 1]]

@[expose] def nfYData : List (List Nat) :=
  [[1, 2, 1, 0, 0, 0, 1, 1, 1], [0, 1, 0, 0, 0, 2, 2, 2, 2], [2, 1, 0, 2, 0, 0, 2, 0, 0],
   [0, 2, 0, 2, 0, 2, 1, 2, 2],
   [1, 0, 0, 1, 2, 1, 0, 1, 0], [2, 2, 1, 1, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0],
   [2, 0, 0, 0, 1, 2, 0, 0, 1]]

@[expose] def nfO (O : Ops (Array Nat) Nat) (R : Array (Array Nat)) (e : List Nat) : Array Nat :=
  O.mul (O.mul (O.mul (O.mul (O.mul (O.mul (O.mul (O.mul
    (O.pow R[bHeisX 0]! (e.getD 0 0)) (O.pow R[bHeisX 1]! (e.getD 1 0)))
    (O.pow R[bHeisX 2]! (e.getD 2 0))) (O.pow R[bHeisX 3]! (e.getD 3 0)))
    (O.pow R[bHeisY 0]! (e.getD 4 0))) (O.pow R[bHeisY 1]! (e.getD 5 0)))
    (O.pow R[bHeisY 2]! (e.getD 6 0))) (O.pow R[bHeisY 3]! (e.getD 7 0)))
    (O.pow R[bHeisZ]! (e.getD 8 0))

@[expose] def heisOK (O : Ops (Array Nat) Nat) (R : Array (Array Nat)) : Bool :=
  decide (2 ≤ bHeisN) && bHeisProg.all (Op.lt bHeisN) &&
    (List.range 4).all (fun i => decide (bHeisX i < bHeisN) && decide (bHeisY i < bHeisN)) &&
    decide (bHeisZ < bHeisN) &&
    (List.range 4).all (fun i => O.cubeOK R[bHeisX i]! && O.cubeOK R[bHeisY i]!) &&
    O.cubeOK R[bHeisZ]! &&
    (List.range 4).all (fun i => O.commOK R[bHeisX i]! R[bHeisZ]! &&
      O.commOK R[bHeisY i]! R[bHeisZ]!) &&
    (List.range 4).all (fun i => O.eq (O.mul R[bHeisX i]! R[bHeisY i]!)
      (O.mul (O.mul R[bHeisY i]! R[bHeisX i]!) R[bHeisZ]!)) &&
    (List.range 4).all (fun i => (List.range 4).all fun j => !decide (i < j) ||
      (O.commOK R[bHeisX i]! R[bHeisX j]! && O.commOK R[bHeisY i]! R[bHeisY j]!)) &&
    (List.range 4).all (fun i => (List.range 4).all fun j => decide (i = j) ||
      O.commOK R[bHeisX i]! R[bHeisY j]!) &&
    O.vne (O.vmul (O.unit 0) R[bHeisZ]!) (O.unit 0)

@[expose] def actOK (O : Ops (Array Nat) Nat) (R : Array (Array Nat)) : Bool :=
  (List.range 2).all (fun k => decide (bG k < bHeisN) && decide (bGInv k < bHeisN)) &&
    (List.range 2).all (fun k => O.eq (O.mul R[bG k]! R[bGInv k]!) O.one &&
      O.eq (O.mul R[bGInv k]! R[bG k]!) O.one) &&
    (List.range 2).all (fun k => (List.range 4).all fun j =>
      O.eq (O.mul (O.mul R[bG k]! R[bHeisX j]!) R[bGInv k]!)
          (nfO O R (nfXData.getD (4 * k + j) [])) &&
        O.eq (O.mul (O.mul R[bG k]! R[bHeisY j]!) R[bGInv k]!)
          (nfO O R (nfYData.getD (4 * k + j) []))) &&
    (List.range 2).all (fun k =>
      O.eq (O.mul (O.mul R[bG k]! R[bHeisZ]!) R[bGInv k]!) (O.mul R[bHeisZ]! R[bHeisZ]!))

@[expose] def zRankOK (R : Array (Array Nat)) : Bool :=
  CFSG.Monster.B.Binary.Native.rankOKOf
    ((List.range 4370).map fun i => (R[bHeisZ]!)[i]! ^^^ (1 <<< i)) 2916

@[expose] def bNFCheckO (O : Ops (Array Nat) Nat) (_ : Unit := ()) : Bool :=
  let R := O.run bHeisProg (O.initRegs (O.decode NativeSporadic.BSeed1)
    (O.decode NativeSporadic.BSeed2) bHeisN)
  heisOK O R && actOK O R && zRankOK R

@[expose] def bNFCheck (_ : Unit := ()) : Bool := bNFCheckO (ops2fr 4370) ()

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
