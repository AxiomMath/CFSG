module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.HarrisSolomonIsoK
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.EvenOuter
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.EvenSporadicStandard.M24Std

theorem harrisSolomonZ2S6IsoK_holds
    (hOB : OddLieA6TwoComponent) (hL : OddA6ModLeaf) (hSpor : SporadicZ2S6Leaf) :
    HarrisSolomonZ2S6IsoK :=
  harrisSolomonZ2S6IsoK_of_inputs CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
    evenLieInvolutionTwoConstrained_holds evenOuterA6LeafMod_holds hOB hL hSpor

end CFSG.EvenSporadicStandard.M24Std
