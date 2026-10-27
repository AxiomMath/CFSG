module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenFourteenThreeCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    3 ∣ Nat.card L → ∀ a : G, a ∈ M → orderOf a = 3 →
    ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ 3 M U) →
    ¬ ⁅Subgroup.zpowers a, L⁆ ≤ pCoreOf 2 L

end CFSG.LocalAnalysis.RankThreeTheoremC
