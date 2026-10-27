module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

@[expose] def classz : WClass where
  rep := [7, 3, 2, 3, 7, 3, 2, 3]
  classSize := 5775
  centOrder := 30720
  centGens := [[1, 2, 1, 6, 3, 7, 5, 6, 5, 7, 5, 3, 3, 6, 2, 3, 7, 6, 7, 4, 5, 1],
    [6, 1, 3, 7, 5, 6, 5, 7, 6, 1, 5, 6, 4, 7, 6, 1]]

@[expose] def classaz : WClass where
  rep := [4, 7, 4, 3, 7, 6, 2, 6, 7, 2, 7, 2, 3, 7, 3, 2, 3, 7, 3, 2, 3]
  classSize := 5775
  centOrder := 30720
  centGens := [[7, 2, 5, 6, 7, 1, 7, 5, 1, 2, 6, 3, 5, 6, 2, 5, 7, 5, 6, 5, 7, 3, 1, 2, 6, 5, 1, 6],
    [5, 6, 1, 2, 1, 6, 3, 7, 5, 6, 5, 2, 7, 1, 6, 5, 3, 7, 3, 4, 5, 1]]

@[expose] def classb : WClass where
  rep := [7]
  classSize := 2200
  centOrder := 80640
  centGens := [[1, 6, 5, 1, 2, 1, 3, 7, 5, 6, 5, 7, 3, 2, 1, 3, 2, 3, 4, 7, 5, 6, 7, 1],
    [1, 6, 5, 2, 1, 6, 3, 2, 7, 2, 7, 6, 3, 5, 3, 1, 2, 1, 4, 7, 3, 5, 4, 2]]

@[expose] def classz₁ : WClass where
  rep := [7, 3, 6, 5, 4, 5, 6, 3, 1, 5]
  classSize := 46200
  centOrder := 3840
  centGens := [[2, 1, 6, 7, 1, 7, 6, 1, 3, 2, 6, 5, 7, 2, 7, 1, 3, 5, 7, 5, 6, 5, 7, 3, 2, 5, 1, 6],
    [5, 3, 7, 3, 4, 6, 1, 3, 1, 2, 5, 3, 7, 2, 7, 3, 6, 7, 2, 7, 2, 3, 5, 6, 1, 2, 1, 6, 5, 6]]

@[expose] def sylow2Words : List (List ℕ) :=
  [[3, 2, 3, 6, 5, 4, 2, 3, 2, 3, 5, 3, 6, 7, 2, 7, 2, 3, 6, 1, 2, 5],
    [4, 7, 4, 5, 7, 3, 4, 6, 1, 2, 3, 2, 3, 7, 5, 6, 5, 7, 3, 1, 2, 1, 5, 6, 1],
    [4, 1, 7, 1, 7, 3, 4, 1, 7, 5, 6, 5, 7, 1, 3, 7, 5, 6, 5, 7, 3, 2, 5, 6, 1],
    [1, 4, 5, 7, 6, 1, 6, 1, 2, 5, 1, 7, 2, 7, 7, 5, 6, 5, 7, 3, 1, 2, 6, 1]]

end CFSG.EvenSporadicStandard.HNRecog
