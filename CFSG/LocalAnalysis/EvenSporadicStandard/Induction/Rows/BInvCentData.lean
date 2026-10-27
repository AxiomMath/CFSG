module

public import Certificates.Data.CFSGNative.CTIB.Census

public section

namespace CFSG.Monster.B.CTIB.Native

@[expose] def censusWord : List Nat → Nat → Nat
  | [], v => v
  | k :: w, v => censusWord w (censusAct k v)

@[expose] def fixesBasis (w : List Nat) : Bool :=
  (List.range 22).all fun i => censusWord w (2 ^ i) == 2 ^ i

@[expose] def movesBasis (w : List Nat) : Bool :=
  (List.range 22).any fun i =>
    censusWord w (2 ^ i) != 2 ^ i && decide (censusWord w (2 ^ i) < 2 ^ 22)

@[expose] def a5WordA : List Nat :=
  [0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1,
   1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0]

@[expose] def a5WordB : List Nat :=
  [1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0,
   1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0]

@[expose] def a5Cycle : List Nat := a5WordB ++ a5WordA

@[expose] def a5OK (_ : Unit) : Bool :=
  a5WordA.all (· < 2) && a5WordB.all (· < 2) &&
    fixesBasis (a5WordA ++ a5WordA) && fixesBasis (a5WordB ++ a5WordB ++ a5WordB) &&
    fixesBasis (a5Cycle ++ a5Cycle ++ a5Cycle ++ a5Cycle ++ a5Cycle) && movesBasis a5WordA &&
    censusWord a5WordA 7 == 7 && censusWord a5WordB 7 == 7

end CFSG.Monster.B.CTIB.Native
