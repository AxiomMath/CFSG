module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017RedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Res
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017TwistCo3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi22
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Baby
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Ly
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Suz
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017ThQ
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Ranks
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017SuzCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Lang.E6Descent.FixedElementary
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Norm
public import CFSG.RankThree.Native.ChainCentralizerD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017


theorem i1017_of_facts (h : I1017Res) (hM3 : I1016M3Fact) (hM5 : I1016M5Fact)
    (G : Type) [Group G] [Finite G] (p : ℕ) : I1017At G p :=
  i1017_of_inputs
    ⟨CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds,
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds,
      i1017TableFact_of_residual3 h.table, i1017CoThreeTwist_holds, h.fi22, h.fi23, h.baby,
      i1017FiTwoTwoAttained_holds, i1017CoverFiTwoTwo_holds, i1017FiTwoThreeAttained_holds,
      i1017BabyAttained_holds,
      i1016RowFacts_of_named i1016LyFact_holds i1016Co2Fact_holds i1016Co1Fact_holds
        i1016Fi24Fact_holds i1016SuzFact_holds i1016ThFact_holds hM3 hM5,
      ⟨i1017LyRank_holds, i1017CoTwoRank_holds, i1017CoOneRank_holds, i1017FiTwoFourRank_holds,
        i1017FiTwoFourCoverRank_holds, i1017SuzRank_holds, i1017SuzCoverRank_holds,
        i1017ThRank_holds, h.m3, h.m5⟩⟩ G p

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
