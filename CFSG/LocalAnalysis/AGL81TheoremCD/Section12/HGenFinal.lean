module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenProof
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCompNonempty

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem not_kSub_le_M_of_nineNineOne {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (hI : NineNineOneInput) [Fact p.Prime] :
    ¬ kSub p M H ≤ M :=
  not_kSub_le_M_of_pLayerIn_le h.not_H_le_M (le_kSub_sup_inf h hI)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
