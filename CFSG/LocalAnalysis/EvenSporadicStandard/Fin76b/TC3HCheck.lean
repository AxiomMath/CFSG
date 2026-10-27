module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TC3H

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native
open CFSG.EvenSporadicStandard.Fin76b.Beta

@[expose] def j2Hex : String := include_str "TC3HJ2.txt"

@[expose] def j3Hex : String := include_str "TC3HJ3.txt"

@[expose] def j2Tbl (k : ℕ) : Table := hexT 3 315 (315 * k) j2Hex

@[expose] def j3Tbl (k : ℕ) : Table := hexT 4 6156 (6156 * k) j3Hex

@[expose] def sqxW (n : ℕ) (x : Array ℕ) (w : List (Array ℕ)) : Bool :=
  allLt n fun i => evR w (x[evR w (x[i]!)]!) == i

@[expose] def commSqxW (n : ℕ) (b x : Array ℕ) (w : List (Array ℕ)) : Bool :=
  commW n [b] w && sqxW n x w

@[expose] def sqrtOK (n : ℕ) (sift : Table → Bool) (u a y : Table) : Bool :=
  permOK n y && (sift y || sift (compT n y u)) && tblEq n (compT n y y) a

@[expose] def j2OuterOK : Bool := zOK 315 j2Sift j2OuterTbl (j2BetaTbl 7) (j2Tbl 0)

@[expose] def j3OuterOK : Bool := zOK 6156 j3Sift j3OuterTbl (j3BetaTbl 7) (j3Tbl 0)

@[expose] def j2CountOuter : ℕ :=
  countW (commSqxW 315 (natArr (j2BetaTbl 7)) (natArr (j2Tbl 0))) PairJ2.blocks []

@[expose] def j3CountOuter : ℕ :=
  PairJ3.parCount (commSqxW 6156 (natArr (j3BetaTbl 7)) (natArr (j3Tbl 0))) PairJ3.blocks

@[expose] def j2SqrtOK : Bool :=
  sqrtOK 315 j2Sift j2OuterTbl (j2CentTbl 31) (j2Tbl 1) &&
    sqrtOK 315 j2Sift j2OuterTbl (j2CentTbl 17) (j2Tbl 2)

@[expose] def j3SqrtOK : Bool := sqrtOK 6156 j3Sift j3OuterTbl (j3CentTbl 9) (j3Tbl 1)

end CFSG.EvenSporadicStandard.Fin76b.TC3H
