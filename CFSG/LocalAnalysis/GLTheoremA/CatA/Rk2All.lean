module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2ETable
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Rank3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2U5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2E6Seven

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open


theorem rk2InnRankOn_of_all (h : Rk2InnRank) (S : GLALabel → Prop) : Rk2InnRankOn S :=
  fun lab hl _ => h lab hl trivial

theorem rk2_inputs_of_tables (T : Rk2Tables) (G : Type) [Group G] [Finite G] :
    I162At G ∧ I163At G ∧ I164At G ∧ ETableAt G ∧ E62At G ∧ RankThreeLabelAt G ∧ U5CaseAt G :=
  ⟨i162At_of_tables T.inn T.lower G, i163At_of_tables T.kRank T.lower T.upper G,
    i164At_of_tables T.split G, eTableAt_of_tables T.kRank T.lower T.upper G, e62At_holds G,
    rankThreeLabelAt_of_tables (rk2InnRankOn_of_all T.inn _) G,
    u5CaseAt_holds G⟩

end CFSG.LocalAnalysis.GLTheoremA
