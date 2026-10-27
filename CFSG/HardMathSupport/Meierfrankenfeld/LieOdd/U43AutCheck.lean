module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvCheck
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutData
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.LieType.Multipliers.U43
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

@[expose] def baseArr : Array Nat := (chainBase.map Fin.val).toArray

@[expose] def dsElt (i j : Nat) : Array Nat := compA 820 (powTab dTab i) (powTab sTab j)

@[expose] def stabElt (gt : List Nat × List Nat) : Array Nat :=
  compA 820 (invCand 820 (wordTab gt.2)) (wordTab gt.1)

@[expose] def cenOK (bp : Nat × List (List Nat × List Nat)) : Bool :=
  bp.2.all (fun gt => isInvA 820 (wordTab gt.2) (invCand 820 (wordTab gt.2)) &&
      (stabElt gt)[bp.1]! == bp.1) &&
    (List.range 820).all fun q => !(bp.2.all fun gt => (stabElt gt)[q]! == q) || q == bp.1

@[expose] def transOK (r : Nat) : Bool :=
  let e := trans[r]!
  (if e.1 == 0 then (wordTab e.2)[0]! == r else (wordTab e.2)[4]! == r)

@[expose] def u43AutCheck (_ : Unit := ()) : Bool :=
  let lev := rawLevels 820 chainS baseArr
  let memN := fun t => siftA 820 lev baseArr 0 t
  isInvA 820 dTab (invCand 820 dTab) && isInvA 820 sTab (invCand 820 sTab) &&
  [dTab, invCand 820 dTab, sTab, invCand 820 sTab].all (fun g =>
    [tabA, tabB].all fun h => memN (conjTab g h)) &&
  (List.range 4).all (fun i => (List.range 2).all fun j =>
    isInvA 820 (dsElt i j) (invCand 820 (dsElt i j)) &&
    (List.range 4).all fun k => (List.range 2).all fun l =>
      (i == k && j == l) || !memN (compA 820 (invCand 820 (dsElt i j)) (dsElt k l))) &&
  cenGens.all cenOK &&
  decide (cenGens.map (·.1) = [0, 4]) &&
  (List.range 820).all transOK

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
