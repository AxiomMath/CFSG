module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Alt8Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Final3
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputThird
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem ega81Lemmas214to217_of_red
    (h : Ega81Lemmas214to217Red) : Ega81Lemmas214to217 := by
  intro hA hHS G _ _ L z hKS hZ hstd hs A B C D hF
  exact wreathData_of_FFzData (h hHS G L z hKS hZ hstd hs A B C D hF
    (layer_of_normalizer_D hA (hF.nData.isKGroupCat_egQD hKS) hs hF.pair.octad hF.octad
      hF.nData (alt8Data_of_type hF.pair.octad)))

theorem ega81Wreath_of_red
    (hHS : HarrisSolomonZ2S6IsoK) (h2 : Ega81Lemmas214to217Red) : Ega81Wreath :=
  ega81Wreath_of_secondHalf hHS (ega81Lemmas214to217_of_red h2)

theorem m24_not_standard_of_secondHalfRed {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hA : Ega81HypAZ2A8K) (hHS : HarrisSolomonZ2S6IsoK) (h2 : Ega81Lemmas214to217Red)
    (h : StdHyp G L) : ¬ IsSporadic L .M24 :=
  m24_not_standard_of_wreath hA (ega81Wreath_of_red hHS h2) h

end CFSG.EvenSporadicStandard.M24Std
