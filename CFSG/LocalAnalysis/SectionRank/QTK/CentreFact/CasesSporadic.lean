module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Sporadic
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.McL
import CFSG.Sporadic.J4
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup CFSG.Blueprint

theorem oddBound_of_sporadic_cover
    {G : Type} [Group G] [Finite G] (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥Y) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : r ∣ Nat.card (center ↥Y)) {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨
      s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL)
    (e : ↥Y ⧸ center ↥Y ≃* NativeSporadic.Carrier s) : OddBound r (↥Y ⧸ center ↥Y) := by
  have hJ4 : J4OrderHyp := dvd_of_eq CFSG.Sporadic.J4.card_J4
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oddBound_of_M11 e hr hr2
  · exact absurd hrZ (not_dvd_card_center_of_M12 hq e hr hr2)
  · exact oddBound_of_M22 e hr hr2
  · exact oddBound_of_M23 e hr hr2
  · exact absurd hrZ (not_dvd_card_center_of_M24 hq e hr hr2)
  · exact oddBound_of_J1 e hr hr2
  · exact absurd hrZ (not_dvd_card_center_of_J2 hq e hr hr2)
  · exact oddBound_of_J3 e hr hr2
  · exact absurd hrZ (not_dvd_card_center_of_J4 hJ4 hq e hr hr2)
  · exact absurd hrZ (not_dvd_card_center_of_HS hq e hr hr2)
  · exact absurd hrZ (not_dvd_card_center_of_He hq e hr hr2)
  · exact absurd hrZ (not_dvd_card_center_of_Ru hq e hr hr2)
  · by_cases hr3 : r = 3
    · subst hr3
      exact absurd hrZ (not_three_dvd_card_center_of_McL he e)
    · exact absurd hrZ (not_dvd_card_center_of_McL_ne_three hq e hr hr3)

end CFSG.SectionRank.QTK.CentreFact
