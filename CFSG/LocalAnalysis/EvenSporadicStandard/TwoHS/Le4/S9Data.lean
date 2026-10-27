module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Data

public section

namespace CFSG.EvenSporadicStandard.TwoHS

@[expose] def sigWords : List (List ℕ) :=
  [[5, 2, 4, 5, 3, 2, 3, 6, 3, 2, 3, 4, 2, 5, 4],
   [2, 1, 3, 2, 3, 6, 3, 2, 3, 1, 2],
   [2, 3, 2, 3, 4, 6, 3, 2, 3, 2],
   [3, 2, 3, 4, 5, 3, 2, 3, 4, 3, 6, 5, 1, 6, 4, 3, 2, 5, 3, 4],
   [3, 2, 3, 4, 1, 2, 3, 1, 2, 3, 2, 1, 5, 4, 3, 2, 1, 6, 5, 1, 6, 4, 3, 2, 3, 2, 1, 4],
   [2, 3, 4, 1, 2, 3, 1, 6, 3, 4, 1, 2, 3, 1, 2]]

@[expose] def betaWords : List (List ℕ) :=
  [[1, 3, 2, 1, 3, 2, 3, 4, 3, 2, 3, 5, 4, 3, 2, 6, 3, 5, 4, 2, 1, 6, 1, 2, 5, 6],
   [3, 4, 5, 2, 3, 2, 6, 5, 1, 2, 3, 6, 1, 2, 3, 5, 6],
   [6, 3, 5, 2, 3, 4, 6, 3, 4, 5, 6, 3, 4, 2, 3, 2, 5, 3, 2, 4, 3]]

@[expose] def tWord : List ℕ := [3, 4, 2, 3, 5, 2, 3, 2, 4, 3, 6, 5, 1, 6, 4, 2, 1, 5, 6]

@[expose] def gamma1Word : List ℕ := [1, 2, 3, 2, 3, 6, 3, 1, 6, 2, 3]

@[expose] def gamma2Word : List ℕ := [6, 5, 1, 4, 3, 2, 3, 4, 1, 2, 1]

@[expose] def gamma1Data : List ℕ := [3, 2, 0, 2, 2, 2, 0, 1, 2, 2, 1, 2, 2, 1, 0, 2]

@[expose] def gamma2Data : List ℕ := [2, 1, 0, 1, 3, 0, 0, 1, 0, 2, 3, 0, 1, 0, 0, 2]

@[expose] def gamma1Mat : M4 := matOfList gamma1Data

@[expose] def gamma2Mat : M4 := matOfList gamma2Data

end CFSG.EvenSporadicStandard.TwoHS
