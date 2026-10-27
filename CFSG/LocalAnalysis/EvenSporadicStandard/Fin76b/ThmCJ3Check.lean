module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne.J3

@[expose] def sylXGens : Array Table := j3SylowGenTbls.toArray

@[expose] def sylXList : Array Table := (mulClosureH 6156 sylXGens 256).1

@[expose] def j3OuterCheck : Bool :=
  sylXList.any (fun x => tblEq 6156 x t0) &&
    sylXList.all (fun x => !(sylXGens.all fun g => commTT 6156 x g) ||
      tblEq 6156 x (idT 6156) || tblEq 6156 x t0) &&
    sylXList.any (fun x => tblEq 6156 (compT 6156 (compT 6156 x x) (compT 6156 x x)) t0 &&
      j3Sift x)

end CFSG.EvenSporadicStandard.Fin76b.J3
