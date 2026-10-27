module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Cor
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoCentral
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2Cent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2A
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2C
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2Rank
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2J
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallCover
public import CFSG.LocalAnalysis.ComponentClassification.KProperComponentLocalBOpen
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBTable517
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Cover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SubSet
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SubS3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFL4Syl
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4h

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem lemma71_ne_of_inputs_sub (hS : SchreierFor Blueprint.Catalog) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexReduced) (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hDC : CFDoubleCover)
    (hRec : CFSp4RecognitionCI) (hCov : CFSp4CoverInv) (hConj : CFSp4Conj) (hComp : CFSp4Comp)
    (hOut : CFSp4Outer) (hCent : CFL2Cent) (hD : CFSp4D) (hA : CFL2A) (hC : CFL2C)
    (hRank : CFL2Rank) (hSyl : CFL2Sylow) (hJ : CFL2J)
    (hW : ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW)
    (hCIS : ClassicalInvolutionStatement71) (X : Type) [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h : Hyp52 X) (hmax : GSMaximalUnbalancingTriple h.a h.x h.J)
    (hiso : GSIsoAt h.a h.J)
    (hnB1 : ¬ ConclusionB1 h.J) (hnB2a : ¬ ConclusionB2a h.a h.J) (hTab : h.Table517)
    (hKa : conjugate h.K h.a ≠ h.K) : False := by
  obtain ⟨s, hy, hrel⟩ := Seven.exists_setting_sub hS hB1 hB6 hCF23 hCF24 hCFc hCFi hCI hUc hDC
    hRec hCov hW hnonab hK hz hU h hmax hiso hnB1 hnB2a hTab hKa
  have hNS := s.normalizer_le hConj hComp hOut hCent hD hA hC hRank hSyl hJ
  obtain ⟨b, hb⟩ := (s.toData hConj hComp hOut hCent).step5 hNS
  obtain ⟨δ, J', hδ, hJδ, hJ', hδJ', hrank, hwit⟩ := hCIS X hnonab hK hz hU h hmax hiso hnB1
    hnB2a hTab hKa s hy hrel hNS b ⟨hb.hb2, hb.hbx, hb.hU2, hb.hbB0, hb.hyb, hb.hcomm, hb.hidx⟩
  exact intrinsic_rank_one_exclusion hCI hUc hnonab hz hU hδ hJδ hJ' hδJ' hrank hwit

theorem cor72_of_inputs_sub
    (hS : SchreierFor Blueprint.Catalog) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexReduced) (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hDC : CFDoubleCover)
    (hRec : CFSp4RecognitionCI) (hCov : CFSp4CoverInv) (hConj : CFSp4Conj) (hComp : CFSp4Comp)
    (hOut : CFSp4Outer) (hCent : CFL2Cent) (hD : CFSp4D) (hA : CFL2A) (hC : CFL2C)
    (hRank : CFL2Rank) (hSyl : CFL2Sylow) (hJ : CFL2J) (hT517 : Table517Statement)
    (hheld : KProperRelativeB.HeldInput) (hCTI : LayerGeneratedUniversalComponentStandard)
    (hRS : RestrictedStandardInput) (hB7 : EmbedsTQuotStatement) (hST : SuzukiTausskyInput)
    (hRecStd : CFSp4RecognitionStd) (hTwo : CFSp4TwoCentral)
    (hCIS : ClassicalInvolutionStatement71) :
    Cor72Statement := by
  have hW := noFusionW_of_inputs hS hUc hheld hCTI
  intro X _ _ _ hnonab hK hz hU h hmax hiso hnB1 hnB2a hTab
  have hne := lemma71_ne_of_inputs_sub hS hB1 hB6 hCF23 hCF24 hCFc hCFi hCI hUc hDC hRec hCov
    hConj hComp hOut hCent hD hA hC hRank hSyl hJ hW hCIS X hnonab hK hz hU
  rcases hTab with h1 | h2 | h3 | h4
  · exact (hne h hmax hiso hnB1 hnB2a (.inl h1) h1.1).elim
  · exfalso
    obtain ⟨p, f, hp, hp2, hf, h5, hJL, hKa, hKL⟩ := id h2
    obtain ⟨h₂, ha, hJ, hmax₂, hKa₂⟩ :=
      Seven.lemma71_step3_sub hS hB1 hB6 hCF23 hCF24 hCFc hCFi hCI hUc hDC hheld hCTI hRS hB7 hST
        hRecStd hTwo hW hCov hnonab hK hz hU h hmax hiso hnB1 hnB2a (.inr (.inl h2)) hp hp2 hf h5
        hJL hKa hKL
    have hiso₂ : GSIsoAt h₂.a h₂.J := by
      rw [ha, hJ]
      exact hiso
    have hnB1₂ : ¬ ConclusionB1 h₂.J := by rw [hJ]; exact hnB1
    have hnB2a₂ : ¬ ConclusionB2a h₂.a h₂.J := by rw [ha, hJ]; exact hnB2a
    exact hne h₂ hmax₂ hiso₂ hnB1₂ hnB2a₂
      (hT517 X hnonab hK hz hU h₂ hmax₂ hiso₂ hnB1₂ hnB2a₂) hKa₂
  · exact .inl h3
  · exact .inr h4

theorem cor72_of_open_inputs_sub
    (hS : SchreierFor Blueprint.Catalog) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCFi : CFProp23IndexReduced)
    (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hRec : CFSp4RecognitionCI)
    (hPP : Sp4CenterPPartInput) (hT517 : Table517Statement)
    (hCTI : UnbalancedCorr.LayerGeneratedUniversalComponentStandard)
    (hRS : RestrictedStandardInput) (hRecStd : CFSp4RecognitionStd)
    (hCIS : ClassicalInvolutionStatement71) :
    Cor72Statement :=
  cor72_of_inputs_sub hS (conjFixStatement_of_inputs hS hUc KProperRelativeB.heldInput)
    sylowKernelStatement hCF23 hCF24 hCFc hCFi hCI hUc
    CatFactsSmall.cfDoubleCover hRec (Catalog7Cover.cfSp4CoverInv hPP) CatFactsSp4.cfSp4Conj
    CatFactsSp4.cfSp4Comp CatFactsSp4.cfSp4Outer AutL2Facts.cfL2Cent CatFactsSp4.cfSp4D
    AutL2Facts.cfL2A
    AutL2Facts.cfL2C AutL2Facts.cfL2Rank AutL2Facts.cfL2Sylow AutL2Facts.cfL2J hT517
    KProperRelativeB.heldInput hCTI hRS embedsTQuotStatement suzukiTausskyInput hRecStd
    CatFactsSp4.cfSp4TwoCentral hCIS

end CFSG.ComponentClassification.GSThmB
