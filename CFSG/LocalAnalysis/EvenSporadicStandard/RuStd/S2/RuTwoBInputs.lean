module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.RuSchreier
open CFSG.EvenSporadicStandard.TwoRu.HypOne

@[expose] def twoBWordG : List ℤ := [1, 2, 3]

@[expose] def twoBWordH : List ℤ := [2, 1, 2]

@[expose] def twoBWordU : List ℤ :=
  [-2, -3, -1, -2, -3, -1, -3, -2, -1, -2, -3, -2, -1, -3, -1, -3, -1, -2, -3, -2, -1, -2, -3, -2,
    -3, -1, -2, -1]

@[expose] def twoBTab (w : List ℤ) : Table := wordT 4060 (letterTab lGens lGensInv) w

@[expose] def twoBComm : Table :=
  compT 4060 (compT 4060 (compT 4060 (twoBTab twoBWordG) (twoBTab twoBWordH))
    (invT 4060 (twoBTab twoBWordG))) (invT 4060 (twoBTab twoBWordH))

@[expose] def ruTwoBCheck : Bool :=
  invOK 4060 (twoBTab twoBWordG) (invT 4060 (twoBTab twoBWordG)) &&
    invOK 4060 (twoBTab twoBWordH) (invT 4060 (twoBTab twoBWordH)) &&
    ordTest 4060 5 twoBComm && ordTest 4060 2 (twoBTab twoBWordU) &&
    !tblEq 4060 (twoBTab twoBWordU) (tblOfArr ruA0A) &&
    allLt lGens.size fun k => commT 4060 (twoBTab twoBWordU) lGens[k]!

end CFSG.EvenSporadicStandard.RuStd.S2
