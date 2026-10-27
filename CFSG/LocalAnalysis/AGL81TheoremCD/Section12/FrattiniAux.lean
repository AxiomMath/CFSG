module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1517bBase

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_of_normal_le {d : ℕ} [Fact d.Prime] {M J N : Subgroup G}
    (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M) (hJM : ¬ J ≤ M)
    (hN : (N.subgroupOf J).Normal) (hNJ : N ≤ J) (hNM : N ≤ M) :
    ¬ d ∣ Nat.card N := by
  intro hdvd
  exact hJM (CFSG.LocalAnalysis.RankThreeUC.S15.O1517b.le_of_normal_of_dvd_of_strong
    Fact.out hN hNJ hNM hdvd hstr)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
