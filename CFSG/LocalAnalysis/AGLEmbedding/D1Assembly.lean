module

public import CFSG.LocalAnalysis.AGLEmbedding.AltBeta
public import CFSG.LocalAnalysis.AGLEmbedding.AltAlpha
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem d1_of_kFacts_of_cases (hβ : KFactBeta) (hα : KFactAlphaW) (h1s : D1CaseOneSmall)
    (h1l : D1CaseOneLie) (h2 : D1CaseTwo) (h3 : D1CaseThree) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Open.IsKProper G)
    (hchar : Open.IsCharTwoType G) (he : 4 ≤ Open.evenRank G)
    (hpre : Open.GLBPreuniqueness G) (p : ℕ) (hp : p ∈ Open.GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : Open.GLBIsMaxTwoLocal M)
    (hWM : Open.GLBWeakCore p (P : Subgroup G) ≤ M) (H : Subgroup G) (hH : Open.IsTwoLocal H)
    (hHM : 3 ≤ Open.pRank p (H ⊓ M)) : H ≤ M :=
  d1_of_kFactsW_of_componentCaseInd hβ hα (d1ComponentCaseInd_of_cases hβ h1s h1l h2 h3) G hnonab
    hK hchar he hpre p hp P M hM hWM H hH hHM

theorem d1_of_lieW_spor_of_cases (hβl : KFactBetaLie)
    (hβs : KFactBetaSpor) (hαl : KFactAlphaLieW) (hαs : KFactAlphaSpor) (h1s : D1CaseOneSmall)
    (h1l : D1CaseOneLie) (h2 : D1CaseTwoRankThree) (h3 : D1CaseThreeNotKlingen) (G : Type)
    [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : Open.IsCharTwoType G) (he : 4 ≤ Open.evenRank G)
    (hpre : Open.GLBPreuniqueness G) (p : ℕ) (hp : p ∈ Open.GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : Open.GLBIsMaxTwoLocal M)
    (hWM : Open.GLBWeakCore p (P : Subgroup G) ≤ M) (H : Subgroup G) (hH : Open.IsTwoLocal H)
    (hHM : 3 ≤ Open.pRank p (H ⊓ M)) : H ≤ M :=
  have hβ := kFactBeta_of_families kFactBetaAlt kFactBetaA6 hβl hβs
  have hα := kFactAlphaW_of_families kFactAlphaAlt hαl hαs
  d1_of_kFacts_of_cases hβ hα h1s h1l (d1CaseTwo_of_rankThree hβ h2)
    (d1CaseThree_of_notKlingen_of_kFactsW hβ hα h3) G hnonab hK hchar he hpre p hp P M hM hWM H
    hH hHM

end CFSG.AGLEmbedding
