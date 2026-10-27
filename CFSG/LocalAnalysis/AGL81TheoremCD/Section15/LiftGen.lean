module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15

theorem liftRankBound_of_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h11 : CFSG.LocalAnalysis.RankThreeUC.S15.Row1511 G M T T₁ T₂)
    (h18 : CFSG.LocalAnalysis.RankThreeUC.S15.Row1518 G M T T₁ T₂) :
    CFSG.LocalAnalysis.RankThreeUC.S15.LiftRankBound G M T T₁ T₂ := by
  refine ⟨?_, ?_⟩
  · exact ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h11
  · intro Ls L hLs hL r hr hr2
    by_cases hrσ : r ∈ sigmaSet G M
    · exact (h18 r hrσ Ls L hLs hL).le
    · exact (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans
        (ctx.rank_odd_off r hr hr2 hrσ)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
