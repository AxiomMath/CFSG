module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksCheck

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open CFSG.Monster.B.Co2.Native

@[expose] def commA : List (List Int) :=
  [[-1, 2], [-1, -2, 1], [-2, -2, 1, 1], [2, 1, 2, -1]]

@[expose] def commB : List (List Int) :=
  [[1, 2, -1], [1, -2], [-2, 1], [2, 1, -2, -1]]

@[expose] def rhoXY : List (List Int) :=
  [[1, -2, -2, 1, -2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, -2, 1, -2, 1, 2, 2],
   [2, -1, -2, -2, -1, -2, -2, -2, -2, 1, -2, 1, -2, -2, -1, -2]]

@[expose] def rhoTau : List (List Int) :=
  [[-1, -2, -1, -2, 1, 2, -1, -2, -2, -1, 2, -1, -1, -2, -2, -1, -1, 2, 2, -1, -1],
   [-1, -1, -2, 1, -2, 1, -2, 1, 1, 2, 2, 2, 2, 2, 1]]

@[expose] def eMask : Nat := 345

@[expose] def mMask : Nat := 678

@[expose] def checkPerf (_ : Unit := ()) : Bool :=
  let S : Array (Array Nat) := Array.ofFn (n := 2) fun j => genArr (j.val + 1)
  let Si : Array (Array Nat) := Array.ofFn (n := 2) fun j => invCand 3510 S[j.val]!
  let a : Array (Array Nat) := Array.ofFn (n := 4) fun s => wordA 3510 S Si (commA.getD s.val [])
  let b : Array (Array Nat) := Array.ofFn (n := 4) fun s => wordA 3510 S Si (commB.getD s.val [])
  let ai : Array (Array Nat) := Array.ofFn (n := 4) fun s => invCand 3510 a[s.val]!
  let bi : Array (Array Nat) := Array.ofFn (n := 4) fun s => invCand 3510 b[s.val]!
  let u : Array (Array Nat) := Array.ofFn (n := 4) fun s =>
    compA 3510 (compA 3510 a[s.val]! b[s.val]!) (compA 3510 ai[s.val]! bi[s.val]!)
  commA.length == 4 && commB.length == 4 && commA.all (lettersOK 2) && commB.all (lettersOK 2) &&
    allLt 2 (fun j => isInvA 3510 S[j]! Si[j]!) &&
    allLt 4 (fun s => isInvA 3510 a[s]! ai[s]! && isInvA 3510 b[s]! bi[s]!) &&
    eqA 3510 (compA 3510 u[0]! u[1]!) S[0]! && eqA 3510 (compA 3510 u[2]! u[3]!) S[1]!

@[expose] def checkRho (_ : Unit := ()) : Bool :=
  let X : Array (Array Nat) := Array.ofFn (n := 2) fun j => xyfArr[j.val]!
  let Xi : Array (Array Nat) := Array.ofFn (n := 2) fun j => invCand 45 X[j.val]!
  let T0 : Array (Array Nat) := tauArrs ()
  let T : Array (Array Nat) := Array.ofFn (n := 2) fun j => T0[j.val + 1]!
  let Ti : Array (Array Nat) := Array.ofFn (n := 2) fun j => invCand 45 T[j.val]!
  rhoXY.length == 2 && rhoTau.length == 2 && rhoXY.all (lettersOK 2) && rhoTau.all (lettersOK 2) &&
    allLt 2 (fun j => isInvA 45 X[j]! Xi[j]!) && allLt 2 (fun j => isInvA 45 T[j]! Ti[j]!) &&
    allLt 2 (fun j => eqA 45 (wordA 45 X Xi (rhoXY.getD j [])) T[j]!) &&
    allLt 2 (fun j => eqA 45 (wordA 45 T Ti (rhoTau.getD j [])) X[j]!)

@[expose] def xorCols (cols : Array Nat) (c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => xorCols cols c n ^^^ (if c.testBit n then cols[n]! else 0)

@[expose] def actCols (k : Nat) : Array Nat :=
  Array.ofFn (n := 10) fun j => actCodes.getD (10 * k + j.val) 0 % 2 ^ 10

@[expose] def applyCols (cols : Array Nat) (c : Nat) : Nat := xorCols cols c 10

@[expose] def lead (v : Nat) : Nat := Nat.log2 v

@[expose] def reduce (B : List Nat) (v : Nat) : Nat :=
  B.foldl (fun v b => if v.testBit (lead b) then v ^^^ b else v) v

@[expose] def ins (r : Nat) : List Nat → List Nat
  | [] => [r]
  | b :: B => if lead b < lead r then r :: b :: B else b :: ins r B

@[expose] def addVec (B : List Nat) (v : Nat) : List Nat :=
  let r := reduce B v
  if r == 0 then B else ins r B

@[expose] def spinStep (f g : Nat → Nat) (B : List Nat) : List Nat :=
  B.foldl (fun acc b => addVec (addVec acc (f b)) (g b)) B

@[expose] def spinBasis (f g : Nat → Nat) (x : Nat) : List Nat :=
  (List.range 12).foldl (fun B _ => spinStep f g B) [x]

@[expose] def dotN (m y : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => dotN m y n != (m.testBit n && y.testBit n)

@[expose] def dotM (m y : Nat) : Bool := dotN m y 10

@[expose] def spinCheck (f g : Nat → Nat) (e m : Nat) : Bool :=
  decide (0 < e) && decide (e < 1024) && !dotM m e &&
    allLt 1024 fun x => x == 0 || x == e ||
      (let B := spinBasis f g x
       let dx := dotM m x
       allLt 1024 fun y => reduce B y == 0 || (!dx && dotM m y))

@[expose] def checkLattice (_ : Unit := ()) : Bool :=
  let C1 := actCols 1
  let C2 := actCols 2
  checkPerf () && checkRho () && spinCheck (applyCols C1) (applyCols C2) eMask mMask

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
