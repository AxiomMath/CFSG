module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutCheck
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43OutData

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.LieType.Multipliers.U43
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

@[expose] def letTab8 (l : Nat) : Array Nat :=
  if l < 4 then letTab l else if l = 4 then dTab else if l = 5 then sTab
  else if l = 6 then invCand 820 dTab else invCand 820 sTab

@[expose] def wordTab8 (w : List Nat) : Array Nat :=
  w.foldl (fun t l => compA 820 t (letTab8 l)) (idA 820)

@[expose] def tGens : List (Array Nat) := pGens ++ tExtraWords.map wordTab8

@[expose] def tTab (k : Nat) : Array Nat :=
  treeTab (idA 820) (mulStep tGens) tPar tLab (2 * tGens.length) fuel k

@[expose] def nonSmall (t : Array Nat) : Bool :=
  witWords.any fun w =>
    let u := compA 820 t (conjTab (wordTab w) t)
    [1, 2, 3, 4, 5].all fun k => !(eqA 820 (powTab u k) (idA 820))

@[expose] def pairOK (memN : Array Nat → Bool) (t₁ t₂ : Array Nat) : Bool :=
  !(eqA 820 (compA 820 t₁ t₂) (compA 820 t₂ t₁)) || memN (compA 820 t₁ t₂) ||
    nonSmall t₁ || nonSmall t₂ || nonSmall (compA 820 t₁ t₂)

@[expose] def u43OutCheck (_ : Unit := ()) : Bool :=
  let lev := rawLevels 820 chainS baseArr
  let memN := fun t => siftA 820 lev baseArr 0 t
  let ks := (List.range 1024).filter fun k => isInvol (tTab k) && !memN (tTab k)
  decide (0 < tGens.length) &&
  (List.range tGens.length).all (fun j => isInvA 820 tGens[j]! (invCand 820 tGens[j]!)) &&
  distinctOK tTab 1024 &&
  closedOK tTab tTbl 1024 (2 * tGens.length) (mulStep tGens) &&
  witWords.all (fun w => isInvA 820 (wordTab w) (invCand 820 (wordTab w))) &&
  ks.all fun k₁ => ks.all fun k₂ => pairOK memN (tTab k₁) (tTab k₂)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out
