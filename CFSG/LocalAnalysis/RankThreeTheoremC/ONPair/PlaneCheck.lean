module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelCheck

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.RankThree.Native

@[expose] def planeInv : Array (Nat × Nat × Nat × Nat) :=
  #[(1, 3, 2, 1), (2, 6, 0, 2), (6, 3, 6, 1), (5, 2, 6, 4), (3, 5, 5, 4), (0, 6, 4, 2),
    (6, 2, 1, 4), (4, 5, 3, 4), (3, 5, 2, 3), (2, 1, 0, 2), (5, 3, 1, 1), (0, 4, 3, 1),
    (4, 6, 4, 5), (1, 4, 5, 1), (0, 4, 4, 6), (1, 1, 2, 5), (6, 2, 6, 3), (3, 6, 5, 2),
    (4, 4, 2, 6), (2, 3, 0, 1), (5, 1, 0, 5), (5, 1, 1, 5), (4, 3, 3, 1), (3, 1, 4, 5),
    (0, 5, 3, 4), (6, 5, 5, 4), (2, 4, 6, 6), (1, 6, 1, 2)]

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
