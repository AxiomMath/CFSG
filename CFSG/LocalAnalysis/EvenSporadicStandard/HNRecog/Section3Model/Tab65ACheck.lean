module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVCheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def tab65ASpec : List (ℕ × ℕ) := [(1, 3), (2, 1)]

@[expose] def tab65AWord : List ℕ :=
  specWord ((tab6Row 5).stabWords classaz.centGens) tab65ASpec

@[expose] def tab65AW : List ℕ :=
  [7, 4, 3, 7, 5, 4, 6, 1, 3, 6, 3, 5, 2, 1, 6, 3, 5, 3, 6, 7, 2, 7, 2, 3, 2, 6]

@[expose] def tab65AOK : Bool :=
  gensOK && wordOK tab65AWord && conjEqOK tab65AW (tabW wordB) (tabW tab65AWord)

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
