module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinCheck

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native
  CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.Induction

@[expose] def suzWordN : List Int :=
  [
  2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2, -1, -2, -1, -2,
  -1, 2, -1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1,
  -2, 1, 2, 1, 2, 1, 2, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2,
  -1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, -1, -2,
  -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1,
  2, -1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2,
  1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2]

@[expose, irreducible] def suzArrN : Array Nat := suzArr suzWordN

@[expose, irreducible] def suzArrNi : Array Nat := invCand 1782 suzArrN

@[expose, irreducible] def suzArrE1 : Array Nat :=
  compA 1782 (compA 1782 suzArrN (tArr 0)) suzArrNi

@[expose, irreducible] def suzArrSigma : Array Nat := suzArr suzWordD

@[expose] def suzCommutes (u v : Array Nat) : Bool :=
  eqA 1782 (compA 1782 u v) (compA 1782 v u)

@[expose] def suzE0Check : Bool :=
  lettersOK 2 suzWordN && lettersOK 2 suzWordD && isInvA 1782 suzArrN suzArrNi &&
    eqA 1782 (compA 1782 suzArrN (compA 1782 suzArrN suzArrN)) (idA 1782) &&
    !eqA 1782 suzArrN (idA 1782) &&
    suzCommutes suzArrN suzArrA && suzCommutes suzArrN suzArrB &&
    eqA 1782 (compA 1782 suzArrE1 suzArrE1) (idA 1782) &&
    suzCommutes (tArr 0) suzArrE1 && !eqA 1782 suzArrE1 (tArr 0) &&
    eqA 1782 (compA 1782 (compA 1782 suzArrN suzArrE1) suzArrNi) (compA 1782 (tArr 0) suzArrE1) &&
    suzCommutes suzArrE1 suzArrA && suzCommutes suzArrE1 suzArrB &&
    suzCommutes suzArrSigma (tArr 0) && !suzCommutes suzArrSigma suzArrE1

end CFSG.EvenSporadicStandard.Solomon78
