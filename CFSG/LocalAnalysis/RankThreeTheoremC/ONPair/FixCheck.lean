module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelCheck
public import CFSG.Sporadic.ONOddCore.PrimCheckInputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.RankThree.Native CFSG.Sporadic.ONOddCore
  CFSG.Sporadic.ON.Native

@[expose] def u2Word : List Int :=
  [-2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2,
    -2, -1, -2]

@[expose] def n1Word : List Int :=
  [1, 2, 1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 2, 2]

@[expose] def n2Word : List Int :=
  [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 2, -1]

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
