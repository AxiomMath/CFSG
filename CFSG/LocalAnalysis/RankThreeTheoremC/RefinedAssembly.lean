module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Leaves3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3ReeRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3KFactsCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerFused2_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericUniquePlaneRank2
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericStructureParts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericQuasisimple3NoBM
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1Red
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34SDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28PartsS
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6AutData
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Consumer
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Derive
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627WMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wResDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43A6
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5FPF
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wMain
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wExists
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Solvable
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Main
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Main
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43M11
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43L34
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34S
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6ActProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28InvProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3TopNoWC
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6PropS
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VIPoint
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem rankThreeUC_of_refined_inputs (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
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
    (hU43 : GL83GenericPrimeThreeU3Lemma43 G) (hA43 : GL83GenericPrimeThreeA6Lemma43VI G)
    (hE43 : GL83GenericPrimeThreeL28Lemma43S G)
    (hNA : GL83Generic4_9BNonabS G)
    (hL34R : GL83GenericPrimeThreeL34Remark G)
    (hR2 : GL83GenericListExclusionRedSpor G)
    (hU3 : GL83GenericU3Plane G) (hKU3 : KFactU3Involution)
    (hFPF : FPFSolvable)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK5 : GL83Generic5KFacts)
    (hEv : KFactCoprimeAutEvenCentralizer)
    (hKPsz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hKcons : SmallRankConstraintKFact3)
    (hKblock : KFactBlockFactorThreePrime) (hKirr : KFactSylowNormalizerIrreducible)
    (hKout : KFactOutThreePrimeSimple) (hKrk2 : KFactRankTwoUniqueness)
    (hKrk3 : KFactRankThreeStructure) (hKcamp : KFactCampbell)
    (hK13 : KFactLemma2813) (hKab : KFactAbelianSylowRankThree)
    (hInt : GL83SmallRankInterfaceW G) (hK628 : KFactZAction628) (hK629 : KFactZAction629)
    (h622 : GL83SmallRankProp622 G) (h630 : GL83SmallRankLemma630Res G) :
    CFSG.Open.rankThreeUC G :=
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
  have hlayer : GL83GenericLayer G :=
    gl83GenericLayer_of_inputs_redNoBM hS hD1' hU0 hK1 hK2 hK3 hKF1
      (genericPrimeThree_of_kfacts_nowc hS hU0 hD1' hK1 hK2 hK3 hKC hK5.innerAction
        hK5.weakClosure hKM11 hKA11 hKT11 hKsig
        (noExcludedSection3_of_sections hk.sections he) hKL hKU hKA6a hKA6b hKA6c hKL28a hKL28b
        hKL28c a6SylowAction_proved hKUb hKA6e l28SylowInversion_proved
        (GL83GenericPrimeThreeLemma43.of_S
          (GL83GenericPrimeThreeM11Shape.of_kfacts hS hU0 hD1' hKM11 hKA11 hKT11 hKsig)
          (GL83GenericPrimeThreeLemma43S.of_parts
            (m11Lemma43S_of_kfacts hS hU0 hD1' hKM11 hKA11 hKT11 hK5.innerAction
              hK5.weakClosure hK3)
            (l34Lemma43_of_remark hS hU0 hD1' hKL.twoSignalizer hKL.three hKL.sylowTransitive
              hL34R)))
        hU43
        (GL83GenericPrimeThreeA6Lemma43.of_S
          (GL83GenericPrimeThreeA6ShapeVI.of_kfacts hS hU0 hD1' hK1 hK2 hK3 hKC
            (noExcludedSection3_of_sections hk.sections he) hKM11 hKA11 hKL hKA6b hKA6c hKL28a
            hKL28c a6SylowAction_proved hKA6e)
          (GL83GenericPrimeThreeA6Lemma43S.of_VI hS hU0 hD1' hKA6b a6SylowAction_proved
            hK5.innerAction hK5.weakClosure hK3 hA43))
        (GL83GenericPrimeThreeL28Prop34SNoWC.of_kfacts hS hU0 hD1' hK1 hK2 hK3 hKC
          (noExcludedSection3_of_sections hk.sections he) hKM11 hKA11 hKL hKA6b hKA6c hKL28a
          hKL28c) hE43 hNA
        hL34R)
      (GL83GenericListExclusionRed.of_e3 he
        (GL83GenericListExclusionRedE3.of_split
          (genericListExclusionRedU3_of_plane hS hD1' hU0 hKU3 hU3) hR2))
      (noExcludedSection3_of_sections hk.sections he)
  have hG5 : Gen5Global G := ⟨hS, hD1', hD2', hU0, hlayer⟩
  have hExcl : NoExcludedSection3 G := noExcludedSection3_of_sections hk.sections he
  have hStr : GL83GenericStructure G :=
    gl83GenericStructure_of_min hS hD1' hU0 hlayer
      (gl83GenericStructureMin_of_res hS hD1' hU0 hlayer
        (gl83GenericStructureRes_of_parts hS hD1' hD2' hU0 hlayer hFPF
          (gl83GenericSolvable_of_kfacts hG5 hK1 hSch hK5 hEv hExcl)
          (gl83GenericFPF_of_kfacts hG5 gl83Generic5CaseI_holds gl83Generic5CaseII_holds hK1 hSch
              hK5 hExcl)))
  have h627w : GL83SmallRankProp627W G :=
    prop627W_of_coreW hS hU0 hKab hSch hK5.innerAction hKrk2 hKrk3 hInt hK628 hK629 h622
      (h630.toCore hS)
  have h627 : GL83SmallRankProp627 G :=
    prop627_of_prop627W hKPsz hKcons hKrk2 hKrk3 hS hU0 h627w
  have h614' : GL83SmallRankProp614 G :=
    prop614_of_k_facts hS hU0 hD2' hKblock hKirr hKout hKrk2 hKrk3 h627
      (prop632_of_prop627 hKPsz hKcons hS hU0 h627) hKcamp hK13
  rankThreeUC_of_inputs G hnonab hK hchar he hpre hD1' hD2' hI hII hcon h13' hrel hlayer
    (genericUniquePlane_of_rank2 hS hD1' hU0 hlayer
      (genericUniquePlaneRank2_of_k5facts hG5 hStr hK5)) hStr
    (smallPrimeThree_of_prop627 hS hU0 h627)
    (smallStructure_of_prop632 hS hU0 (prop632_of_prop627 hKPsz hKcons hS hU0 h627))
    (smallQ8_of_prop627 hS hU0 hD2' h627 h614')
    (smallUniquePlane_of_prop627 hS hU0 hD2' h627 h614')

end CFSG.LocalAnalysis.RankThreeTheoremC
