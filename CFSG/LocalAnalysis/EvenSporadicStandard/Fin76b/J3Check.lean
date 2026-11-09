module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.FstR

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne.J3

@[expose] def sylList : Array Table := fstR (mulClosureH 6156 sgP0 128)

theorem sylList_fst : sylList = (mulClosureH 6156 sgP0 128).1 :=
  (rfl : sylList = fstR (mulClosureH 6156 sgP0 128)).trans (fstR_eq _)

@[expose] def j3CenterCheck : Bool :=
  sylList.any (fun x => tblEq 6156 x t0) &&
    sylList.all (fun x => !(sgP0.all fun g => commTT 6156 x g) ||
      tblEq 6156 x (idT 6156) || tblEq 6156 x t0) &&
    sylList.any (fun x => tblEq 6156 (compT 6156 x x) t0)

end CFSG.EvenSporadicStandard.Fin76b.J3
