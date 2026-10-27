module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinData

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native
  CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.Solomon78

@[expose] def suzArrWord (w : List Int) : Array Nat := wordA 1782 suzArrAB suzArrABi w

@[expose] def suzCommArr (u v : Array Nat) : Array Nat :=
  compA 1782 (compA 1782 (compA 1782 u v) (invCand 1782 u)) (invCand 1782 v)

@[expose] def suzKCheck : Bool :=
  enumOK 1782 suzArrAB (enumOf 1782 suzArrAB 20160) &&
    (enumOf 1782 suzArrAB 20160).tabs.size == 20160

@[expose] def suzCommOK (u v t : Array Nat) : Bool :=
  isInvA 1782 u (invCand 1782 u) && isInvA 1782 v (invCand 1782 v) && eqA 1782 (suzCommArr u v) t

@[expose] def suzPerfCheck : Bool :=
  suzCommOK (suzArrWord suzWordU1) (suzArrWord suzWordV1) suzArrA &&
    suzCommOK (suzArrWord suzWordU2) (suzArrWord suzWordV2) suzArrB

@[expose] def suzE8Check : Bool :=
  let a := suzArrWord suzWordE1
  let b := suzArrWord suzWordE2
  let c := suzArrWord suzWordE3
  eqA 1782 (compA 1782 a a) (idA 1782) && eqA 1782 (compA 1782 b b) (idA 1782) &&
    eqA 1782 (compA 1782 c c) (idA 1782) &&
    eqA 1782 (compA 1782 a b) (compA 1782 b a) && eqA 1782 (compA 1782 a c) (compA 1782 c a) &&
    eqA 1782 (compA 1782 b c) (compA 1782 c b) &&
    !eqA 1782 a (idA 1782) && !eqA 1782 b (idA 1782) && !eqA 1782 b a &&
    !eqA 1782 c (idA 1782) && !eqA 1782 c a && !eqA 1782 c b &&
    !eqA 1782 c (compA 1782 a b)

@[expose] def suzCommCheck : Bool :=
  eqA 1782 (compA 1782 (suzArr suzWordC) (tArr 0)) (compA 1782 (tArr 0) (suzArr suzWordC)) &&
    eqA 1782 (compA 1782 (suzArr suzWordD) (tArr 0)) (compA 1782 (tArr 0) (suzArr suzWordD)) &&
    suzCommOK (suzArr suzWordC) (suzArr suzWordD) (tArr 0)

@[expose] def suzPinLetters : Bool :=
  lettersOK 2 suzWordE1 && lettersOK 2 suzWordE2 && lettersOK 2 suzWordE3 &&
    lettersOK 2 suzWordU1 && lettersOK 2 suzWordV1 && lettersOK 2 suzWordU2 &&
    lettersOK 2 suzWordV2 && lettersOK 2 suzWordC && lettersOK 2 suzWordD &&
    suzArrA.size == 1782 && suzArrB.size == 1782

@[expose] def suzPinCheck : Bool :=
  suzPinLetters && suzE8Check && suzPerfCheck && suzCommCheck && suzKCheck

end CFSG.EvenSporadicStandard.Induction
