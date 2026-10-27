module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint

theorem sporOddCompsAny_M22
    : SporOddCompsAny .M22 :=
  fun _ _ _ _ _ e t ht B hB =>
    not_oddLieOrder_card_quotient_center_of_card_dvd (a := 7)
      ((RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
        (RestrictedStd.Spor.isoInvariant_card_dvd 384) RestrictedStd.Spor.m22_centralizerIn_comps
        e t ht B hB).trans (by norm_num))

theorem sporOddCompsAny_M23
    : SporOddCompsAny .M23 :=
  fun _ _ _ _ _ e t ht B hB =>
    not_oddLieOrder_card_quotient_center_of_not_three_dvd
      (RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
        RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.m23_centralizerIn_comps
        e t ht B hB)

theorem sporOddCompsAny_M24
    : SporOddCompsAny .M24 :=
  fun _ _ _ _ _ e t ht B hB =>
    not_oddLieOrder_card_quotient_center_of_not_three_dvd
      (RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
        RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.m24_centralizerIn_comps
        e t ht B hB)

theorem sporOddCompsAny_Ru
    : SporOddCompsAny .Ru :=
  fun _ _ _ _ _ e t ht B hB =>
    not_oddLieOrder_card_quotient_center_of_not_three_dvd
      (RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
        RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.ru_centralizerIn_comps
        (e.trans Sporadic.RuSchreier.ruEquivP) t ht B hB)

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
