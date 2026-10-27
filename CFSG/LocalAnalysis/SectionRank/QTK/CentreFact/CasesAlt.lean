module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Alt9

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup

theorem oddBound_of_alternating_cover {G : Type} [Group G] [Finite G]
    (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : r ∣ Nat.card (center ↥Y)) {n : ℕ} (hn : n ≤ 9)
    (e : ↥Y ⧸ center ↥Y ≃* alternatingGroup (Fin n)) : OddBound r (↥Y ⧸ center ↥Y) := by
  rcases Nat.lt_or_ge n 9 with h8 | h9
  · exact oddBound_of_alternating (by omega) e hr hr2
  · obtain rfl : n = 9 := by omega
    by_cases hr3 : r = 3
    · subst hr3
      exact absurd hrZ (not_three_dvd_card_center_of_alt_nine he e)
    · exact oddBound_of_alternating_nine_of_ne_three e hr hr2 hr3

end CFSG.SectionRank.QTK.CentreFact
