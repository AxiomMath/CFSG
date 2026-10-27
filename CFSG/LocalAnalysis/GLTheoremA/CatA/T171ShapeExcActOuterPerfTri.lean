module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfAssemble
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (twistedFixedPoints d4Nodes D4TrialityLayer)



theorem excRankFourTrialityPerfect_holds : ExcRankFourTrialityPerfect := by
  intro τ L _ _ _ p S a hT i hk hr
  cases τ with
  | G2 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨-, hA | ⟨-, hc, -⟩⟩ := exc_kind hk
    · rw [hA.1] at hr
      exact absurd hr (by decide)
    · obtain ⟨N, hN, hNL, hTN⟩ := excTri_exists_order S hT
      exact (excTri_F4_absurd hN hNL hTN i hr hc).elim
  | D4 => exact excTri_perfect_D4 S i hk hr
  | E6 => exact excTri_perfect_E6 S hT i hk hr
  | E7 => exact excTri_perfect_E7 S hT i hk hr
  | E8 => exact excTri_perfect_E8 S hT i hk hr

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
