module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C5

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem row1512 (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSMAlt : KSMAlt)
    (hK541 : K541) (hKParU5 : KParU5) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : Row1512 G M T T₁ T₂ := by
  intro Ls L hLs hL
  have h3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3 := fun r hr hr2 =>
    (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (ctx.rank_odd r hr hr2)
  have hdat := rankDatum1512_of_rankDatum (rankDatum hT ctx.gn ctx.shape hLs hL) h3
  refine ⟨isGroupOf1512_of_datum hKSMOdd hKSMU4 hKSMAlt hK541 ctx.gn ctx.shape hLs hL hdat h3, ?_⟩
  intro hU h5
  obtain ⟨d, Q, hQ, hc, hd, e⟩ := quotCenter_of_isUFiveFour hU
  rcases two_le_mN_of_u5 hKParU5 ctx.gn (S15Ctx2.good ctx) hLs.1 hQ hc hd e with h | h
  · exact (Nat.not_lt.2 (ctx.rank_N₁ 5 h5)) h
  · exact (Nat.not_lt.2 (ctx.rank_N₂ 5 h5)) h

end CFSG.LocalAnalysis.RankThreeUC.S15
