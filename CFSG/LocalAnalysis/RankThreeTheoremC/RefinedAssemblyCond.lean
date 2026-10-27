module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RefinedAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC


theorem rankThreeUC_of_refined_inputs_cond (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Open.IsKProper G)
    (hchar : CFSG.Open.IsCharTwoType G) (he : CFSG.Open.evenRank G = 3)
    (hpre : CFSG.Open.rankThreeAschCoreLocal G 2) (hβ : KFactBetaRank2)
    (hk : D1CaseThreeKFactsCore3)
    (hc : D1CaseThreeChevFacts3) (hD1 : D1FrontierResidues3 G) (hA3 : D1AlphaKFacts3)
    (hD2K : D2KFactLeaves) (hD2 : D2Leaves3 G)
    (hgen : CentralizerGenerationThree G)
    (hKsig : SignalizerTwoGroupKFact)
    (hKF1 : KF1At G) (hKF3 : ZLayerWeakCoreFact3) (hB3 : Bal3KFacts)
    (hZJ1 : KFactZJFactorization) (hZJ2 : KFactAlmostSimpleRankTwo)
    (hK1 : StronglyEmbeddedRankTwoKFactNoBM)
    (hK2 : StronglyEmbeddedCyclicOuterKFact) (hK3 : KFactOutCyclic)
    (hKC : KFactComponentPCoreThree)
    (hKM11 : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA11 : KFactM11TwoSignalizer)
    (hKT11 : KFactM11SylowTransitive) (hKL : KFactsL34Full) (hKU : KFactU3TwoSignalizer)
    (hKUb : KFactU3SylowInversion) (hKA6a : KFactA6TwoSignalizer) (hKA6b : A6SylowData)
    (hKA6c : A6BorelCore) (hKA6e : A6AutData)
    (hKL28a : KFactL28Three) (hKL28b : KFactL28FieldSignalizer)
    (hKL28c : KFactL28BorelCore)
    (hU43 : TheoremD1 G → FullCoreLocal G → GL83GenericPrimeThreeU3Lemma43 G)
    (hA43 : TheoremD1 G → FullCoreLocal G → GL83GenericPrimeThreeA6Lemma43VI G)
    (hE43 : TheoremD1 G → FullCoreLocal G → GL83GenericPrimeThreeL28Lemma43S G)
    (hNA : TheoremD1 G → FullCoreLocal G → GL83Generic4_9BNonabS G)
    (hL34R : TheoremD1 G → FullCoreLocal G → GL83GenericPrimeThreeL34Remark G)
    (hR2 : TheoremD1 G → FullCoreLocal G → GL83GenericListExclusionRedSpor G)
    (hU3 : TheoremD1 G → FullCoreLocal G → GL83GenericU3Plane G) (hKU3 : KFactU3Involution)
    (hFPF : FPFSolvable)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK5 : GL83Generic5KFacts)
    (hEv : KFactCoprimeAutEvenCentralizer)
    (hKPsz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hKcons : SmallRankConstraintKFact3)
    (hKblock : KFactBlockFactorThreePrime) (hKirr : KFactSylowNormalizerIrreducible)
    (hKout : KFactOutThreePrimeSimple) (hKrk2 : KFactRankTwoUniqueness)
    (hKrk3 : KFactRankThreeStructure) (hKcamp : KFactCampbell)
    (hK13 : KFactLemma2813) (hKab : KFactAbelianSylowRankThree)
    (hInt : TheoremD1 G → TheoremD2 G → FullCoreLocal G → GL83SmallRankInterfaceW G)
    (hK628 : KFactZAction628) (hK629 : KFactZAction629)
    (h622 : TheoremD1 G → TheoremD2 G → FullCoreLocal G → GL83SmallRankProp622 G)
    (h630 : TheoremD1 G → TheoremD2 G → FullCoreLocal G → GL83SmallRankLemma630Res G) :
    CFSG.Open.rankThreeUC G := by
  have hS : Setting G := ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩
  have hD1' : TheoremD1 G :=
    hD1.theoremD1 hS (KFactsA3.of_sections hβ hk.sections he) (alphaNone_of_list hA3 hKF1)
      hk.toKFacts d1CaseThreeReeFacts3 hc
  have hD2' : TheoremD2 G :=
    theoremD2_of_componentCase3 hS hD1' (d2ComponentCase3_of_max (hD2.componentCaseMax3 hD2K))
  have hcon : TransitivityComponentCase G := transitivityComponentCase_of_kfacts3 hS hKF1 hKF3
  have hGen : CentralizerGeneration G := centralizerGeneration_of_three hS hKF1 hgen
  have hI : SignalizerCentralNonConstrained G :=
    signalizerCentralNonConstrained_of_generation hS hGen
  have hII : SignalizerNoncentralPart G := signalizerNoncentralPart_of_irreducible hS hI
    (signalizerNoncentralIrreducible_of_narrow hS
      (signalizerNoncentralLocalNarrow_of_fused hS hD1' hK1 hK2
        (noExcludedSection3_of_sections hk.sections he) hKsig
        (signalizerNoncentralFused_of_generation hS hGen)))
  have hred := transitivityReduction_of_componentCase hS hcon
  have h13' : GL83InvariantTwoSylow G := gl83InvariantTwoSylow_of_within hS hred
    (gl83InvariantTwoWithin_of_bal hS hD1' hKF1
      (bal_of_bal3 hS hD1' (bal3_of_kfacts hS hD1' hB3)))
  have hrel : GL83RelativePairExclusion G :=
    gl83RelativePairExclusion_of_relPair2A7Module hS hD1' hB3.lemma212 hred h13'
      (gl83RelPair2Thompson_of_alt hS hD1' hred h13'
        (gl83RelPair2ThompsonAlt_of_kfacts hS hD1' hred h13' hZJ1 hZJ2))
      (gl83RelPair2A7Module_proved hS)
  have hU0 : FullCoreLocal G := fullCoreLocal_of_cases hS hD1' (signalizerCase_of_parts hS hI hII)
    (transitivityCase_of_containment hS hD1' hred h13'
      (gl83InvariantTwoContainment_of_relativePairExclusion hS hD1' hred h13' hrel))
  exact rankThreeUC_of_refined_inputs G hnonab hK hchar he hpre hβ hk hc hD1 hA3 hD2K hD2 hgen
    hKsig hKF1 hKF3 hB3 hZJ1 hZJ2 hK1 hK2 hK3 hKC hKM11 hKA11 hKT11 hKL hKU hKUb hKA6a hKA6b
    hKA6c hKA6e hKL28a hKL28b hKL28c (hU43 hD1' hU0) (hA43 hD1' hU0) (hE43 hD1' hU0)
    (hNA hD1' hU0) (hL34R hD1' hU0) (hR2 hD1' hU0) (hU3 hD1' hU0)
    hKU3 hFPF hSch hK5 hEv hKPsz hKcons hKblock hKirr hKout hKrk2 hKrk3 hKcamp hK13 hKab (hInt hD1' hD2' hU0)
    hK628 hK629 (h622 hD1' hD2' hU0) (h630 hD1' hD2' hU0)

end CFSG.LocalAnalysis.RankThreeTheoremC
