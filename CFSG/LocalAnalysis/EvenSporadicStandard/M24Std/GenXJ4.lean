module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.FusionInterface
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXFinal

public section

namespace CFSG.EvenSporadicStandard.M24Std.GenX

theorem ega81M24Section_of_secondHalf
    (hFH : FirstHalfProp) (hHS : HarrisSolomonZ2S6IsoK) (h2 : Ega81Lemmas214to217) :
    CFSG.EvenSporadicStandard.J4Std.Ega81M24Section :=
  fun hA X _ _ hKX z K hzz hz1 hK hKz hC hnc =>
    section_of_secondHalf hFH hHS h2 hA X hKX z K hzz hz1 hK hKz hC hnc

theorem ega81M24Section_of_secondHalf'
    (hHS : HarrisSolomonZ2S6IsoK) (h2 : Ega81Lemmas214to217) :
    CFSG.EvenSporadicStandard.J4Std.Ega81M24Section :=
  ega81M24Section_of_secondHalf firstHalfProp hHS h2

end CFSG.EvenSporadicStandard.M24Std.GenX
