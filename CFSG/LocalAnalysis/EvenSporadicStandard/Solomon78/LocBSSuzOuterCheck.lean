module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuterData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuterData

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native
  CFSG.PSL3Four.Native

@[expose, irreducible] def suzArrM0 : Array Nat := suzArr suzWordM0

@[expose, irreducible] def suzArrV0 : Array Nat := compA 1782 suzArrM0 vArr

@[expose, irreducible] def suzTabV0 : Tab := restrictArr (fixList 0) suzArrV0

@[expose] def suzRangeTabs : Array Tab := (enumOf 42 (kGens 0) 40320).tabs

@[expose] def suzCentCheck : Bool := centralOK 42 suzRangeTabs dGens

@[expose] def suzCosetCheck : Bool :=
  allBelow suzRangeTabs.size fun k =>
    !(allBelow dGens.size fun j =>
      comp 42 (comp 42 suzTabV0 suzRangeTabs[k]!) dGens[j]! ==
        comp 42 dGens[j]! (comp 42 suzTabV0 suzRangeTabs[k]!))

@[expose] def suzOuterRelOK : Bool :=
  lettersOK 2 suzWordM0 &&
  eqA 1782 (compA 1782 suzArrV0 (tArr 0)) (compA 1782 (tArr 0) suzArrV0)

@[expose] def suzOuterCheck : Bool := suzOuterRelOK && suzCentCheck && suzCosetCheck

end CFSG.EvenSporadicStandard.Solomon78
