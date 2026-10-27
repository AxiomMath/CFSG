module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbStep5Odd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbStep5Gold
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbStep5Count
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

theorem iibStep5_of
    (hGold : Asc76X.GoldschmidtTheoremA) :
    IIbStep5 := by
  intro G _ _ A R g T V₀ P t z₀ a σ c₁ hS _ hD
  have hA := IIbData.caseA hGold hS hD
  have hO := IIbData.oddCoreIn_centralizer_eq_bot hGold hS hD
  exact hD.step5_of_normal hS hA hO (hD.centralizer_le_normalizer_E₁ hGold hS hA hO)

theorem asc310IIbStep56 :
    Asc310IIbStep56 :=
  asc310IIbStep56_of (iibStep5_of Asc76X.goldschmidtTheoremA)

end CFSG.ComponentClassification.RankTwoAltFive
