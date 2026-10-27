module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrameData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def planeMasks : List ℕ :=
  [15, 51, 60, 85, 90, 102, 105, 150, 153, 165, 170, 195, 204, 240]

@[expose] def planeThrough (a b c : ℕ) : ℕ :=
  (planeMasks.find? fun m => m.testBit a && m.testBit b && m.testBit c).getD 0

@[expose] def frame16CheckWith (RA FA : Array (Array ℕ)) : Bool :=
  allLt 240 (fun r => !memE1 FA RA[r]! || (List.range 8).any fun i =>
    r == keyPts.getD i 0 || r == negArr[keyPts.getD i 0]!) &&
  allLt 8 (fun i => allLt 8 fun j => i == j ||
    (keyPts.getD i 0 != keyPts.getD j 0 && keyPts.getD i 0 != negArr[keyPts.getD j 0]!))

@[expose] def frame16Check : Bool := frame16CheckWith reflArrs frameArrs

end CFSG.EvenSmallLie.OmegaEight.Weyl
