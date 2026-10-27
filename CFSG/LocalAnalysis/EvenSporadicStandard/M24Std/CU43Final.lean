module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Residue
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXJ4Red
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.L44AtlasAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.L44AtlasRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.L44AtlasFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Main

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem m24_not_standard_of_gold {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hA : Ega81HypAZ2A8K) (hHS : HarrisSolomonZ2S6IsoK) (hG : Goldschmidt74Cor4)
    (h : StdHyp G L) :
    ¬ IsSporadic L .M24 :=
  m24_not_standard_of_secondHalfRed hA hHS
    (red_of_residue atlasL44Aut atlasL44ThreeRank atlasL44FixedPoints
      (ega81Residue_of_cU43 hG (residue_cU43 hG))) h

end CFSG.EvenSporadicStandard.M24Std

namespace CFSG.EvenSporadicStandard.M24Std.GenX

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem j4_not_standard_of_gold {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hA : Ega81HypAZ2A8K) (hHS : HarrisSolomonZ2S6IsoK) (hG : Goldschmidt74Cor4)
    (h : StdHyp G L) :
    ¬ IsSporadic L .J4 :=
  j4_not_standard_of_secondHalfRed hA hHS
    (red_of_residue atlasL44Aut atlasL44ThreeRank atlasL44FixedPoints
      (ega81Residue_of_cU43 hG (residue_cU43 hG))) h

end CFSG.EvenSporadicStandard.M24Std.GenX
