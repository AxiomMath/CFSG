module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Holds
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.OBHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.OddHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.SporHolds

public section

namespace CFSG.EvenSporadicStandard.M24Std

theorem harrisSolomonZ2S6IsoK_proved :
    HarrisSolomonZ2S6IsoK :=
  harrisSolomonZ2S6IsoK_holds oddLieA6TwoComponent_holds oddA6ModLeaf_holds
    sporadicZ2S6Leaf_holds

end CFSG.EvenSporadicStandard.M24Std
