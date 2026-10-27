module

public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PinData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PinData

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block

@[expose] def co1GenArr : Array (Array Nat) := #[twoBStrong[0]!, twoBStrong[1]!]

@[expose] def co1GenInv : Array (Array Nat) :=
  #[invCand 1365 twoBStrong[0]!, invCand 1365 twoBStrong[1]!]

@[expose] def co1ArrWord (w : List Int) : Array Nat := wordA 1365 co1GenArr co1GenInv w

@[expose] def co1E8Check : Bool :=
  let a := co1ArrWord co1WordE1
  let b := co1ArrWord co1WordE2
  let c := co1ArrWord co1WordE3
  isInvA 1365 twoBStrong[0]! (invCand 1365 twoBStrong[0]!) &&
    isInvA 1365 twoBStrong[1]! (invCand 1365 twoBStrong[1]!) &&
    lettersOK 2 co1WordE1 && lettersOK 2 co1WordE2 && lettersOK 2 co1WordE3 &&
    eqA 1365 (compA 1365 a a) (idA 1365) && eqA 1365 (compA 1365 b b) (idA 1365) &&
    eqA 1365 (compA 1365 c c) (idA 1365) &&
    eqA 1365 (compA 1365 a b) (compA 1365 b a) && eqA 1365 (compA 1365 a c) (compA 1365 c a) &&
    eqA 1365 (compA 1365 b c) (compA 1365 c b) &&
    !eqA 1365 a (idA 1365) && !eqA 1365 b (idA 1365) && !eqA 1365 b a &&
    !eqA 1365 c (idA 1365) && !eqA 1365 c a && !eqA 1365 c b &&
    !eqA 1365 c (compA 1365 a b)

end CFSG.EvenSporadicStandard.Induction
