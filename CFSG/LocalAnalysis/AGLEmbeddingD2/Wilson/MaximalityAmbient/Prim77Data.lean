module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77Data

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77

open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77

@[expose] def powA (a : Array Nat) : Nat → Array Nat
  | 0 => idA
  | k + 1 => comp (powA a k) a

@[expose] def lettersData : Array (Array Nat) :=
  #[dataS[0]!, powA dataS[0]! 2, dataS[2]!, powA dataS[2]! 4]

@[expose] def transText : String := ":\n:2\n:3 3\n:3\n:0 2\n:2 2\n:2 0 2\n:1 3 3 1 2\n:1 3 1 2\n:1 3 0 3\n:2 0 3 1 3\n:3 3 0 2 2 1 2\n:0 2 2 0 2\n:3 1 3 1 2\n:2 1 3 0 2\n:0 3 3\n:1 3 0 3 1 2\n:3 3 1 2\n:0 3\n:1 2 2 0 2\n:2 1 3\n:2 0 3\n:1 2 0 2\n:1 3\n:2 0 2 2 1 2\n:0 3 1 3\n:0 3 0 2\n:3 0 3\n:1 3 1 2 0 2\n:1 2\n:3 1 2 0 2\n:1 3 0 2\n:3 1 2\n:3 0 3 1 2\n:2 2 0 2\n:3 3 0 2\n:2 2 1 3\n:3 3 0 3\n:3 3 1 3\n:1 3 3 0 3\n:3 1 3\n:2 1 3 3 0 3\n:3 3 1 3 0 2\n:0 3 0 3 3\n:1 2 0 3\n:2 1 2\n:0 2 0 3\n:3 3 1 2 0 2\n:0 3 0 3\n:2 2 0 2 2 1 2\n:3 1 2 2 0 2\n:0 3 3 1 2\n:2 1 3 1 2\n:2 0 3 1 2\n:2 1 3 0 3\n:2 0 2 0 3\n:3 0 2 0 3\n:2 0 3 0 3\n:3 0 2 2 1 2\n:3 0 3 0 2\n:2 2 1 3 1 2\n:3 1 3 0 2\n:3 3 0 3 1 2\n:0 2 1 3 0 2\n:3 0 3 3\n:3 0 2\n:0 2 2 0 3\n:3 3 1 3 1 2\n:3 3 0 3 3\n:0 3 1 2\n:3 0 3 3 1 2\n:2 2 0 3\n:0 3 3 1 3 1 2\n:2 2 1 2\n:0 2 2 1 2\n:2 0 2 2 0 3\n:2 2 0 3 1 2"

@[expose] def transWords : Array (List Nat) := parseWords transText

@[expose] def repText : String := "0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 24 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 24 1 1 1 1 1 1 1 1 24 1 1 1 24 1 24 24 1 1 24 1 24 1 24 24 1 1 24 24 24 24 24 1 24"

@[expose] def repArr : Array Nat := parseNats repText

@[expose] def stabText : String := ":\n:\n:2 0 3 1 3 1 2 0 3 0\n:1 3 0 3 1 3 3 1\n:0\n:3 3 1 3 0 2 1 2 0\n:2 0 2 0 3 3 0 2\n:0 3 0 3 1 3 3 0\n:1 3 3 1 2 2\n:3 3 0 2 2 0\n:2 2 0 2 1 3 0 2 2 1\n:3 3 0 2 2 1\n:2 2 0 2 1 2 1\n:1 2 2 0 2 1 2\n:2 0 3 3 1 2 2 1 3 0\n:2 1 3 0 2 1 2 0 2 0\n:0 3 0 3 1 3 3\n:1 3 0 3 1 3 3 0\n:3 0 3 1 3 3 1\n:0 2 2 0 2 1 2 1\n:3 1 2 2 1 3 1 3\n:0 2 0 3 0 2 0 2 0\n:1 2 0 2 0 3 3 0 2\n:0 3 0 3 1 3 3 1\n:\n:3 3 1 3 0 2 1 2\n:0 2 2 0 2 1 3 1 2 2 0\n:0 3 3 0 2 2 0\n:0 3 3 1 2 2 1\n:1\n:1 3 3 1 2 2 1\n:1 2 2 0 2 1 3 1 2 2 0\n:3 3 1 2 2\n:1 3 0 3 1 3 3\n:1 2 2 0 2 1 2 1\n:0 3 3 1 3 0 2 1 2\n:3 0 3 1 2 0 2 2\n:2 2 0 2 1 2 0\n:0 2 2 0 2 1 2 0\n:2 0 3 0 2 0 2\n:1 3 3 1 3 0 2 1 2\n:3 3 1 2 2 0\n:3 0 3 1 2 1 2 2 0\n:3 3 0 2 2\n:2 0 3 0 2 0 2 0\n:2 1 2 0 2 0 3 0 2 0\n:3 1 3 1 2 1 3 1\n:0 2 2 0 2 1 2\n:1 3 3 0 2 2 0\n:0 3 3 1 2 2 0\n:3 3 0 3 0 2 1 2\n:3 0 3 1 3 3 0\n:2 0 3 3 1 2 0 2 0 2\n:1 3 3 0 2 2\n:3 3 1 2 2 1\n:3 0 3 1 3 3\n:0 3 3 0 2 2\n:2 2 0 2 1 2\n:1 3 0 3 1 3 3\n:0 3 3 1 2 2\n:0 3 0 3 1 2 1 2 2 0\n:0 3 3 0 2 2\n:0 3 0 3 1 3 3\n:3 3 1 2 0 3 1 3 3\n:1 3 3 0 2 2\n:2 2 0 2 1 3 1 2 2 0\n:2 0 3 1 3 1 2 0 3\n:3 1 2 2 1 3 1 3\n:3 3 0 2 2\n:0 3 3 1 2 2\n:1 3 1 2 2 1 3 1 3\n:2 1 3 0 2 1 2 0 2\n:2 0 3 3 1 2 2 1 3\n:1 3 3 1 2 2\n:3 3 1 2 2\n:1 3 0 3 1 2 1 2 2 0\n:3 0 3 1 3 3"

@[expose] def stabWords : Array (List Nat) := parseWords stabText

@[expose] def w8Word : List Nat := [0, 2, 1, 2, 1, 3]

@[expose] def chkTrans : Bool :=
  transWords.size == 77 &&
    (List.range 77).all fun i => (evalW lettersData (transWords.getD i [])).getD 0 0 == i

@[expose] def chkStab : Bool :=
  stabWords.size == 77 && repArr.size == 77 &&
    (List.range 77).all fun i =>
      i == 0 ||
        (let w := evalW lettersData (stabWords.getD i [])
         w.getD 0 0 == 0 && w.getD (repArr.getD i 0) 0 == i &&
           decide (12 ≤ (List.range 77).countP fun y =>
             decide (y ≠ 0) && repArr.getD y 0 == repArr.getD i 0))

@[expose] def chkOrder (a : Array Nat) (p : Nat) : Bool := a != idA && powA a p == idA

@[expose] def chkOrders : Bool :=
  chkOrder dataS[0]! 3 && chkOrder dataS[2]! 5 && chkOrder dataS[3]! 7 && chkOrder dataS[4]! 11 &&
    (let a := evalW lettersData w8Word
     powA a 4 != idA && powA a 8 == idA)

@[expose] def primCheck : Bool := chkTrans && chkStab && chkOrders

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77
