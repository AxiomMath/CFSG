module

public import CFSG.RankThree.Native.ONThreeInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

open CFSG.RankThree.Native CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def onWitnessCore (a b : Array Nat) : Bool :=
  let u := onSevenPow (pcomp nPts a b) 3
  peq nPts (onSevenPow u 5) (pid nPts) && !(peq nPts u (pid nPts)) &&
    allBelowN 4 (fun k => !(peq nPts (pcomp nPts a u) (pcomp nPts (onSevenPow u (k + 1)) a)))

@[noinline, expose] def onWitnessChecks (_ : Unit := ()) : Bool :=
  onWitnessCore onThreeYArrs[0]! onThreeYArrs[1]!

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native
