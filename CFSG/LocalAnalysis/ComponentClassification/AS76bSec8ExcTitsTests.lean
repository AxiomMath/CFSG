module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTitsData
public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTitsData
public meta import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.TitsSec8

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native

@[expose] def wA (w : List ℤ) : Array ℕ := wordArr 1755 titsDerivedArrs w

@[expose] def mcommA (x y : Array ℕ) : Array ℕ :=
  compA 1755 (compA 1755 (compA 1755 x y) (invCand 1755 x)) (invCand 1755 y)

@[expose] def invOK (x : Array ℕ) : Bool := isInvA 1755 x (invCand 1755 x)

@[expose] def inJ (a : Array ℕ) : Bool := siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 a

@[expose] def wordAt (L : List (List ℤ)) (i : ℕ) : List ℤ := L.getD i []

@[expose] def firstComm (L : List (List ℤ)) : Array ℕ :=
  mcommA (wA (wordAt L 0)) (wA (wordAt L 1))

@[expose] def secondComm (L : List (List ℤ)) : Array ℕ :=
  mcommA (wA (wordAt L 2)) (wA (wordAt L 3))

@[expose] def titsSec8ZCheck : Bool :=
  titsSec8ZWords.length == 4 &&
    titsSec8ZWords.all (fun w => lettersOK 13 w && invOK (wA w) && inH (wA w)) &&
    invOK (firstComm titsSec8ZWords) && invOK (secondComm titsSec8ZWords) &&
    inJ (firstComm titsSec8ZWords) && inJ (secondComm titsSec8ZWords) &&
    eqA 1755 (mcommA (firstComm titsSec8ZWords) (secondComm titsSec8ZWords)) titsZArr

@[expose] def titsSec8TCheck : Bool :=
  titsSec8TWords.length == 4 &&
    titsSec8TWords.all (fun w => lettersOK 13 w && invOK (wA w) && inN (wA w) &&
      commA (wA w) titsTArr) &&
    invOK (firstComm titsSec8TWords) && invOK (secondComm titsSec8TWords) &&
    inK (firstComm titsSec8TWords) && inK (secondComm titsSec8TWords) &&
    eqA 1755 (mcommA (firstComm titsSec8TWords) (secondComm titsSec8TWords)) titsTArr

@[expose] def titsSec8CentreCheck : Bool :=
  titsCCQ.all fun c => !(titsCNt.all fun x => commA c x) || eqA 1755 c (idA 1755) ||
    eqA 1755 c titsTArr || !eqA 1755 (compA 1755 c c) (idA 1755)

@[expose] def titsSec8Check : Bool :=
  titsSec8ZCheck && titsSec8TCheck && titsSec8CentreCheck

end CFSG.ComponentClassification.RankTwoExceptional.TitsSec8
