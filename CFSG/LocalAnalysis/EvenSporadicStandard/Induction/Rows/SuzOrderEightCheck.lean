module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native
  CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.Solomon78

@[expose] def suzWordO8 : List Int := [-2, 1, 2, -1, 2, 1, -2, -1, 2, -1]

@[expose] def suzArrO8 : Array Nat := suzArr suzWordO8

@[expose] def suzOrderEightCheck : Bool :=
  lettersOK 2 suzWordO8 &&
    eqA 1782 (compA 1782 (compA 1782 (compA 1782 suzArrO8 suzArrO8) (compA 1782 suzArrO8 suzArrO8))
      (compA 1782 (compA 1782 suzArrO8 suzArrO8) (compA 1782 suzArrO8 suzArrO8))) (idA 1782) &&
    !eqA 1782 (compA 1782 (compA 1782 suzArrO8 suzArrO8) (compA 1782 suzArrO8 suzArrO8))
      (idA 1782)

end CFSG.EvenSporadicStandard.Induction
