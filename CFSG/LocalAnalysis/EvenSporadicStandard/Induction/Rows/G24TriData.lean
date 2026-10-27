module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBase

public section

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2.Native

@[expose] def triNums : Array Nat := parseNums (include_str "G24TriTbl.txt")

@[expose] def triM (i : Nat) : Nat := triNums[i * 2731]!

@[expose] def triA (i : Nat) : Array Nat := triNums.extract (i * 2731 + 1) (i * 2731 + 1366)

@[expose] def triB (i : Nat) : Array Nat := triNums.extract (i * 2731 + 1366) (i * 2731 + 2731)

@[expose] def triCheck (s : Array Nat) (i : Nat) : Bool :=
  inD (triA i) && inD (triB i) && isInvA nn (triA i) (invCand nn (triA i)) &&
    isInvA nn (triB i) (invCand nn (triB i)) &&
    eqA nn (compA nn (triA i) s) (compA nn s (triA i)) &&
    eqA nn (compA nn (triB i) s) (compA nn s (triB i)) && ordIs (triA i) 2 && ordIs (triB i) 3 &&
    (triM i == 5 || triM i == 7) && ordIs (compA nn (triA i) (triB i)) (triM i)

@[expose] def trianglesOK : Bool := triCheck tAa 0 && triCheck xa 1 && triCheck oa 2

end CFSG.EvenSporadicStandard.G24Aut
