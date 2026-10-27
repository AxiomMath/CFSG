module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightCentral

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

theorem squareCaseHighRankCentralizerImpossible_of_covers
    (hcov : BenderCoverStatement) :
    SquareCaseHighRankCentralizerImpossible := by
  intro G _ _ S H z hsq J hJ hJH hrank hZ hk
  have hs : SzEightSetting S H z J := ⟨hsq, hJ, hJH, hrank, hZ, hk⟩
  have := hs.normal
  rcases hs.cover hcov with he | he
  · exact hs.false_of_psl2 he.some
  · exact hs.false_of_szModel_of_normal he.some

end CFSG.ProperTwoGeneratedCore.Lemma37
