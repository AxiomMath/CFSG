module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.A8LabelData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVCheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def a8WX : List ℕ := specWord classb.centGens a8SX

@[expose] def a8WY : List ℕ := specWord classb.centGens a8SY

@[expose] def a8W0 : List ℕ := specWord classb.centGens a8SU

@[expose] def a8Cap : ℕ := 100000

@[expose] def a8LabelOK : Bool :=
  gensOK && wordOK a8WX && wordOK a8WY && wordOK a8W0 &&
    commutatorEqOK (tabW a8WX) (tabW a8WY) (tabW a8W0) &&
    conjEqOK a8WZ (tabW wordZ) (tabW a8W0) &&
    orbRowOK a8Cap classb.centGens a8W0 80640 a8Row

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
