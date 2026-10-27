module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFourTwoList
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFourTwoExclude

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.LocalAnalysis.RankThreeUC

section Cert


theorem nineFourTwoSigmaGen_holds
    : NineFourTwoSigmaGen := by
  intro G _ _ M Q H E p s hp hL hΓ
  obtain ⟨-, hKn, hX, hXc, -, -⟩ := AGL81C.nineFourTwo_structure s hp hL hΓ
  exact ⟨hKn, hX, hXc, AGL81C.nineFourListGroup_kStar_of_not s hp hL hΓ
    (AGL81C.not_isAltTwoP_kStar s hp hL hΓ) (AGL81C.not_isFi22_kStar s hp hL hΓ)⟩

end Cert

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
