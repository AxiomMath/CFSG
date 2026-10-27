module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4RootCore
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoResT0
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5SwapProof
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormalC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6TightC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6CaseOneC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6U3Four
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Boundary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbFinal
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuLeaf
public import CFSG.Sporadic.Schreier.RuB1Native

public section

namespace CFSG.ComponentClassification.GMS78

open CFSG.ComponentClassification.RankTwoStandard CFSG.Assembly.LowTwoRank

theorem rankTwoBenderStandard_of_open
    (hH1 : RuH1Stmt) : RankTwoBenderStandard := by
  have hHKS := hksRegularNormalAffine
  have hR := gms42ResidualU_of gms42ResidualT0 gms42ResidualRoot
  have hNS := gms5NotSylow_of_key
  have hF : Foundation := ⟨RankTwoFoundation.lemma32, RankTwoFoundation.lemma33One,
    RankTwoFoundation.lemma33Two, RankTwoFoundation.lemma33Three,
    RankTwoFoundation.asc75Theorem4⟩
  have hRu : DempwolffRuMin :=
    dempwolffRuMin_of_open hF CFSG.Sporadic.RuSchreier.ruB1NativeFacts hH1
  have h61 := gms61InductionC_of gms61QuasisimpleC gms61TightC (gms61NotNormalC hF)
    (gms61CaseOneC hF)
  have hL2 := l2Res_of_gms42ResidualU hF hHKS hR
  intro G _ _ A hA hO hT
  rcases hT with ⟨m, hm, hS⟩ | ⟨m, hm, hS⟩ | ⟨m, hm, hS⟩
  · exact absurd hS (not_psl2_of_l2Res hL2 G A hA hO m hm)
  · rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
    · exact (gms6U3Four_of hF RankTwoFoundation.section3Config Asc76X.goldschmidtTheoremA
        gms61TightC (gms61CaseOneC hF) RankTwoAltFive.asc310IIb G A hA hO hS).elim
    · exact (u3_case_of_eight_leC h61 hL2 G A hA hO m hm3 hS).elim
  · obtain ⟨rfl, hX⟩ := sz_case_of_foundation_min hF hHKS hRu hNS gms5Swap G A hA hO m hm hS
    exact ⟨hS, hX⟩

end CFSG.ComponentClassification.GMS78
