module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0BigClose
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieListInvolveWShape
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms


theorem d1OneLieZZK0Big_of_listInvolveW (hK : KFactOneLie) (hTor : KFactOneLieTorus)
    (hSch : KFactCatalogSchreier) (hSC : KFactOneLieSylowCount) (hβ : KFactBeta)
    (hα : KFactAlphaW) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hKl : KFactKlingenSpFour) (hin : KFactChevTwoInnerGen) (hout : KFactChevTwoOuterGen)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hSF : SporCaseThreeKFacts) (hLIW : KFactOneLieListInvolveW)
    (hRC : KFactRankOneCoreProper) (hCO : KFactOneLieCenterOver) (hPR : StmtCoprimeAutRankTwo)
    (hKU1 : KFactUnitarySchur) (hKU2 : KFactUnitarySylowStructure)
    (hKU3 : KFactUnitarySylowCenterTorus) (hKU4 : KFactUnitaryTorusPPD)
    (hKU6 : KFactUnitaryBorelMaximal) (hKU8 : KFactUnitarySylowNormalizerSolvable)
    (hKU9 : KFactUnitaryAutElemRank) (hKR1 : KFactReeSchur) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock)
    (hB3 : StmtBlockThree) (hLB : StmtLemmaBRelCyc) : D1OneLieZZK0Big := by
  intro G _ _ p P M H R Rbar K hd hJ hY hWK hU3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H₁ hH₁ hJH₁ _
    hlt hmax
  exact hd.false_of_kZeroMax_ne_of_comp hK hTor hSC hCO hPR hKU2 hKU3 hKU4 hKU6 hKU8 hKU9 h84 h85
    hD2 hCGT hB3 hLB hJ hY hWK hU3 hH₁ hJH₁ hlt hmax fun _ _ hc hcon =>
      hc.exists_comp_of_listInvolveW hTor hSch hβ hα hP1L hP1A hKl hin hout hOutS hSF hLIW hRC
        hKU1 hKR1 hcon

theorem d1OneLieZZK0Small_of_listInvolveW (hK : KFactOneLie) (hTor : KFactOneLieTorus)
    (hSch : KFactCatalogSchreier) (hSC : KFactOneLieSylowCount) (hβ : KFactBeta)
    (hα : KFactAlphaW) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hKl : KFactKlingenSpFour) (hin : KFactChevTwoInnerGen) (hout : KFactChevTwoOuterGen)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hSF : SporCaseThreeKFacts) (hLIW : KFactOneLieListInvolveW)
    (hRC : KFactRankOneCoreProper) (hCO : KFactOneLieCenterOver) (hPR : StmtCoprimeAutRankTwo)
    (hKU1 : KFactUnitarySchur) (hKU2 : KFactUnitarySylowStructure)
    (hKU3 : KFactUnitarySylowCenterTorus) (hKU4 : KFactUnitaryTorusPPD)
    (hKU6 : KFactUnitaryBorelMaximal) (hKU8 : KFactUnitarySylowNormalizerSolvable)
    (hKU9 : KFactUnitaryAutElemRank) (hKR1 : KFactReeSchur) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock)
    (hB3 : StmtBlockThree) (hLB : StmtLemmaBRelCyc) : D1OneLieZZK0Small := by
  intro G _ _ p P M H R Rbar K hd hJ hY hWK hU3 _ H₁ hH₁ hJH₁ _ hlt hmax
  exact hd.false_of_kZeroMax_ne_of_comp hK hTor hSC hCO hPR hKU2 hKU3 hKU4 hKU6 hKU8 hKU9 h84 h85
    hD2 hCGT hB3 hLB hJ hY hWK hU3 hH₁ hJH₁ hlt hmax fun _ _ hc hcon =>
      hc.exists_comp_of_listInvolveW hTor hSch hβ hα hP1L hP1A hKl hin hout hOutS hSF hLIW hRC
        hKU1 hKR1 hcon

end CFSG.AGLEmbedding
