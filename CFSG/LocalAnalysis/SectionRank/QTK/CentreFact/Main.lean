module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBMain
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.CasesOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.CasesSporadic
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Glue
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.CasesAlt
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.CasesEven
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.U54
public import CFSG.LocalAnalysis.SectionRank.QTK.Section

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup

theorem qtCentreFactSub_holds :
    QTCentreFactSub := by
  intro G _ _ he Y hq hK r hr hr2 hrZ
  have hT : TableRestricted (↥Y ⧸ center ↥Y) r := fun _ _ _ _ hm =>
    CoverB.tablePrime_of_dvd hq hm hr hr2 hrZ
  rcases CoverB.qtkSimpleList_of_cover he hq hK with
    ⟨n, -, hn, ⟨e⟩⟩ | ⟨p, -, -, h⟩ | h | h | ⟨s, hs, ⟨e⟩⟩
  · exact oddBound_of_alternating_cover he hr hr2 hrZ hn e
  · exact oddBound_of_odd_list hr hr2 hT h
  · exact oddBound_of_even_list hr hr2 hT
      (fun hm hr5 => not_five_dvd_card_center_of_U54 he hm (hr5 ▸ hrZ)) h
  · exact oddBound_of_even_high_rank_list hr hT h
  · exact oddBound_of_sporadic_cover he hq hr hr2 hrZ hs e

theorem qtCentreFact_holds :
    QTCentreFact :=
  qtCentreFact_of_sub qtCentreFactSub_holds

end CFSG.SectionRank.QTK.CentreFact
