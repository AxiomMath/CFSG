module

public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.SectionRank.Native CFSG.Blueprint

set_option compiler.extract_closed false

@[expose] def bHeisN : Nat := 136

@[expose] def bHeisProg : List Op := [
    .mul 0 1 2, .mul 2 1 3, .mul 2 2 4, .mul 4 4 5, .mul 5 3 6, .mul 6 6 7, .mul 6 7 8,
    .mul 8 8 9, .mul 9 9 10, .mul 10 10 11, .mul 0 11 12, .mul 12 12 13, .mul 13 6 14,
    .mul 14 6 15, .mul 14 14 16, .mul 15 14 17, .mul 16 17 18, .mul 18 18 19, .mul 18 19 20,
    .mul 19 20 21, .mul 14 15 22, .mul 22 22 23, .mul 6 23 24, .mul 24 24 25, .mul 25 25 26,
    .mul 15 23 27, .mul 27 22 28, .pow 27 28 29, .mul 29 26 30, .mul 30 28 31, .mul 21 31 32,
    .mul 32 31 33, .mul 32 33 34, .mul 32 34 35, .mul 35 32 36, .mul 36 33 37, .mul 32 37 38,
    .mul 34 37 39, .pow 5 39 40, .pow 3 34 41, .pow 17 35 42, .pow 24 38 43, .mul 42 43 44,
    .pow 7 44 45, .mul 45 41 46, .mul 46 44 47, .mul 40 47 48, .pow 10 48 49, .pow 3 40 50,
    .mul 40 49 51, .pow 2 49 52, .mul 52 40 53, .mul 51 50 54, .mul 54 53 55, .pow 7 47 56,
    .mul 47 49 57, .mul 52 47 58, .mul 57 56 59, .mul 59 58 60, .mul 55 60 61, .pow 15 61 62,
    .pow 24 6 63, .mul 62 63 64, .mul 0 64 65, .pow 26 65 66, .pow 5 61 67, .mul 67 67 68,
    .mul 66 68 69, .mul 69 69 70, .pow 5 70 71, .mul 70 68 72, .mul 71 68 73, .mul 72 73 74,
    .mul 74 70 75, .pow 2 75 76, .mul 75 68 77, .mul 76 68 78, .mul 77 78 79, .mul 79 75 80,
    .mul 55 80 81, .pow 20 81 82, .pow 39 81 83, .pow 7 60 84, .mul 84 82 85, .mul 85 60 86,
    .mul 84 86 87, .mul 87 60 88, .mul 84 88 89, .mul 89 60 90, .mul 82 90 91, .mul 81 86 92,
    .mul 92 83 93, .mul 81 93 94, .mul 94 83 95, .mul 84 95 96, .mul 96 60 97, .mul 82 97 98,
    .mul 60 93 99, .mul 99 84 100, .mul 81 100 101, .mul 101 83 102, .mul 82 102 103,
    .mul 60 82 104, .mul 104 84 105, .mul 81 105 106, .mul 106 83 107, .mul 60 107 108,
    .mul 108 84 109, .mul 83 109 110, .mul 110 81 111, .mul 82 111 112, .mul 81 95 113,
    .mul 113 83 114, .mul 82 114 115, .mul 83 88 116, .mul 116 81 117, .mul 82 117 118,
    .mul 84 93 119, .mul 119 60 120, .mul 81 120 121, .mul 121 83 122, .mul 82 122 123,
    .mul 60 105 124, .mul 124 84 125, .mul 60 125 126, .mul 126 84 127, .mul 83 127 128,
    .mul 128 81 129, .mul 82 129 130, .pow 2 91 131, .pow 2 115 132, .mul 131 132 133,
    .mul 133 91 134, .mul 134 115 135]

@[expose] def bHeisX (i : Nat) : Nat := [91, 98, 103, 112].getD i 0

@[expose] def bHeisY (i : Nat) : Nat := [115, 118, 123, 130].getD i 0

@[expose] def bHeisZ : Nat := 135

@[expose] def bHeisCheckO (O : Ops (Array Nat) Nat) (_ : Unit := ()) : Bool :=
  let R := O.run bHeisProg (O.initRegs (O.decode NativeSporadic.BSeed1)
    (O.decode NativeSporadic.BSeed2) bHeisN)
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

@[expose] def bHeisCheck (_ : Unit := ()) : Bool := bHeisCheckO (ops2fr 4370) ()

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
