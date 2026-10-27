module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Conj
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Reduce
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.SplitForm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.SplitGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.NonsplitForm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.NonsplitGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Main

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

theorem pSpFourPPrimeGen : PSpFourPPrimeGen := by
  intro q _ hq2 p hp hp2 hpq
  refine pPrimeGenAt_psp_four_of hq2 hp hp2 hpq fun E hE => ?_
  by_cases h₁ : p ∣ q - 1
  · obtain ⟨P, hP, ζ, hζ, h0, h1⟩ := exists_conj_spDiag hp hp2 hpq hE h₁
    exact closure_fixSetSp_of_le_conj hP le_rfl (closure_fixSetSp_of_spDiag hp hpq hζ h0 h1)
  by_cases h₂ : p ∣ q + 1
  · obtain ⟨P, hP, s₀, hdet, hord, h0, h1⟩ := exists_conj_spPair hp hp2 hpq hE h₂
    exact closure_fixSetSp_of_le_conj hP le_rfl
      (closure_fixSetSp_of_spPair hq2 hp hp2 hpq h₂ hdet hord h0 h1)
  exact (false_of_isElemSp hp hp2 hpq hE h₁ h₂).elim

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
