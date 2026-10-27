module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.Sporadic.J4.QTRankInvData

public section

namespace CFSG.QuasithinUnique.Lin2
open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def invEs : List ℕ := [56, 616, 495, 726]

@[expose] def invCs : List ℕ := [0, 0, 5, 3]

@[expose] def invWords : List (List ℕ) :=
  [[2, 0, 3], [1, 2, 3, 2, 1], [3, 2, 1, 2, 0, 2, 3, 2], [3, 0, 2, 1, 2, 0]]

end CFSG.QuasithinUnique.Lin2
