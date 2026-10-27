module

public import Certificates.Data.CFSGNative.Fi23.Certificate
public meta import Certificates.Data.CFSGNative.Fi23.Certificate

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native

@[expose] def fi23PerfTxt : String := include_str "Fi23Perf.txt"

@[expose] def parseWord (line : String) : List Nat :=
  ((line.splitOn " ").filter (· ≠ "")).map String.toNat!

@[expose] def fi23PerfLines : List String := fi23PerfTxt.splitOn "\n"

@[expose] def fi23PerfM : Nat := fi23PerfLines[0]!.toNat!

@[expose] def fi23PerfGens : List (List Nat) :=
  ((fi23PerfLines.drop 1).take fi23PerfM).map parseWord

@[expose] def fi23PerfX : List Nat := parseWord fi23PerfLines[fi23PerfM + 1]!

@[expose] def fi23PerfY : List Nat := parseWord fi23PerfLines[fi23PerfM + 2]!

@[expose] def fi23G1 : List Nat := [0]

@[expose] def fi23G2 : List Nat := [1, 1, 0, 1, 1, 0, 1]

@[expose] def invLetters : List Nat → List Nat
  | [] => []
  | x :: w => invLetters w ++ (if x = 0 then [0] else [1, 1])

@[expose] def wm (w : List Nat) : Array W := prodW 253 #[matA, matB] w

@[expose] def conjW (g : List Nat) : Array W :=
  mulW 253 (mulW 253 (wm g) matD) (wm (invLetters g))

@[expose] def commW (X Y : Array W) : Bool := eqW 253 (mulW 253 X Y) (mulW 253 Y X)

@[expose] def pairOK (R X Y : Array W) : Bool :=
  commW X R && commW Y R && eqW 253 (mulW 253 X Y) (mulW 253 R (mulW 253 Y X))

@[noinline, expose] def perfCheckOf (g1 g2 : List Nat) (gs : List (List Nat))
    (wx wy : List Nat) : Bool :=
  let D := matD
  let D1 := conjW g1
  let C := conjW g2
  let RB := mulW 253 D D1
  let RC := mulW 253 RB C
  let T : Array (Array W) := (gs.map conjW).toArray
  (g1 :: g2 :: gs).all (fun w => w.all fun x => decide (x < 2)) &&
    (wx ++ wy).all (fun x => decide (x < gs.length)) &&
    commW D D1 && commW D C && commW D1 C && canonW 253 D && canonW 253 D1 && canonW 253 C &&
    !eqW 253 D D1 && !eqW 253 D C && !eqW 253 D1 C &&
    pairOK RB (wm [0]) D1 && T.all (fun t => commW t RC) &&
    pairOK RC (prodW 253 T wx) (prodW 253 T wy)

@[noinline, expose] def fi23PerfCheck : Bool :=
  perfCheckOf fi23G1 fi23G2 fi23PerfGens fi23PerfX fi23PerfY

end CFSG.EvenSporadicStandard.Solomon78
