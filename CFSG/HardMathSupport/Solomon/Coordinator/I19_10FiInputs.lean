module

public import CFSG.RankThree.Native.Fi22FiveArrays
public meta import CFSG.RankThree.Native.Fi22FiveArrays
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Std.Data.HashMap

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def fi22ScalarArr : Array ℕ :=
  compA 3510 (compA 3510 (fi22FiveCGenArrs 3)[1]! (fi22FiveCGenArrs 3)[2]!)
    (compA 3510 (fi22FiveCGenArrs 4)[1]! (fi22FiveCGenArrs 4)[2]!)

@[expose] def fi22ScalarCheck : Bool :=
  eqA 3510 (compA 3510 fi22ScalarArr fi22FiveQ1Arr)
      (compA 3510 (powA 3510 fi22FiveQ1Arr 2) fi22ScalarArr) &&
    eqA 3510 (compA 3510 fi22ScalarArr fi22FiveQ2Arr)
      (compA 3510 (powA 3510 fi22FiveQ2Arr 2) fi22ScalarArr)

end CFSG.HardMathSupport.Solomon.Coordinator
