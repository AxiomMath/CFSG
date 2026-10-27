module

public import CFSG.LocalAnalysis.RankFourTheoremC.Refined
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.AGLEmbedding.D1Local.isCoreMaxLocal {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (h : D1Local p P M) : IsCoreMaxLocal p P M :=
  ⟨h.maxLocal, h.core⟩

theorem theoremD1_of_d1For (h4 : 4 ≤ evenRank G) (hD1 : D1For G) : TheoremD1 G :=
  fun p hp P M hM hcore hmax H hH h3 =>
    hD1 p (mem_betaFour_of_mem_sigmaA h4 hp) P M
      ⟨hM, fun K hK hMK => hmax K hK (hcore.trans hMK) hMK⟩ hcore H hH h3

theorem fullCoreLocal_iff (h4 : 4 ≤ evenRank G) : FullCoreLocal G ↔ FullCoreLocality G :=
  ⟨fun h p P M hloc => h p (mem_sigmaA_of_mem_betaFour hloc.beta) P M hloc.isCoreMaxLocal,
    fun h p hp P M hM => h p P M ⟨mem_betaFour_of_mem_sigmaA h4 hp, hM.1, hM.2⟩⟩

end CFSG.LocalAnalysis.RankFourTheoremC
