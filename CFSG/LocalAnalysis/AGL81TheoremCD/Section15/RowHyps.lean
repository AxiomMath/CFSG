module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def Row1512Datum (G : Type) [Group G] [Finite G] (M T : Subgroup G)
    (T₁ T₂ : Subgroup ↥M) : Prop :=
  ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      RankDatum1512 (T.subgroupOf M) L Ls

@[expose] def RowNotDvdSubOne (G : Type) [Group G] [Finite G] (M T : Subgroup G)
    (T₁ T₂ : Subgroup ↥M) : Prop :=
  ∀ p ∈ sigmaM G M, 5 ≤ p → ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      2 ≤ CFSG.Open.pRank p L → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
        In1512 d.1 → (∀ Q, d.1 = .twistedA 4 Q → p ≠ 5) →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ¬ p ∣ KFactsPair.indexQ d.1 - 1

theorem row1512Datum_of_ctx2 (hT : LieOddRankTable) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) :
    Row1512Datum G M T T₁ T₂ := by
  intro Ls L hLs hL
  exact rankDatum1512_of_rankDatum (rankDatum hT ctx.gn ctx.shape hLs hL) fun r hr hr2 =>
    (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (ctx.rank_odd r hr hr2)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
