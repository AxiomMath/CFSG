module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Final
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L51
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L52
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L53
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L54
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L55
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L56
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Step56
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Glue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L512K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L512H
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L510
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BZClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BFact59Spec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFinal
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L41
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L410
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L43
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L45
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L46
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L47Transfer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L48
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L49
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ZStar
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint


structure Asc82Sec5Inputs3 : Prop where
  tab : Asc82Tab5
  tab56 : Asc82Tab56
  factB : Asc82Sec5FactB5
  fact512K : Asc82Fact512K
  l58b : Asc82Lemma58b
  l58d : Asc82Lemma58d
  f510 : Asc82Fact510
  fact512H : Asc82Fact512H
  l520 : Asc82Lemma520
  facts6 : Asc82Sec5Facts6

theorem aschOmega6MinusZ2_of_inputs3 (h3 : Asc82Sec3Results) (h34a : Asc82Lemma34a)
    (h7 : AschOmega7) (hZ : Asc82ZExists) (hO : Asc82Outside) (i : Asc82Sec5Inputs3) :
    AschOmega6MinusZ2 := by
  intro G _ _ t L hS htwo
  have h : Sec5Setting G t L := { toSec3SettingLB := hS, twoU43 := htwo }
  have h51 : Asc82Lemma51 := asc82Lemma51_of h7 h3.l38 h3.l311
  have h52a : Asc82Lemma52a := asc82Lemma52a_of h3.l33 h51
  have h52b : Asc82Lemma52b := asc82Lemma52b_of h52a
  have h53 : Asc82Lemma53 := asc82Lemma53_of h3.l36 h52a h52b i.tab
  have h54 : Asc82Lemma54 := asc82Lemma54_of h3.l36 h3.l37 h52a h52b h53 i.tab
  have h55 : Asc82Lemma55 := asc82Lemma55_of h3.l36 h3.l37 h52a h52b h53 h54 hO i.tab
  have hs56 : Asc82Step56 := asc82Step56_of h52b h53 h54 h3.l37 hZ i.tab i.tab56
  have h56 : Asc82Lemma56 := asc82Lemma56_of h52b h55 i.tab hs56
  have hy : Sec5B59Hyp := ⟨h3.l36, h3.l37, h52b, h53, i.tab, h54, i.l58b⟩
  have h510 : Asc82Lemma510 := asc82Lemma510_of hy i.l58d asc82Fact59_holds i.f510
  have h512b : Asc82Lemma512b :=
    asc82Lemma512b_of h34a hy h52a i.l58d asc82Fact59_holds i.f510 i.facts6.pockets
      i.facts6.qcent i.facts6.frame i.facts6.outZeta
  obtain ⟨S, z, r, B, A, hr⟩ := sec5_exists_rctx h52b h56 hZ i.factB h
  have hc : centerIn L = zpowers t := h512b G t L S z r B A hr
  obtain ⟨K₁, K₂, hK⟩ := asc82Lemma512K_of i.fact512K G t L S z r B A hr hc
  obtain ⟨h', hH⟩ := asc82Lemma512H_of h3.l36 h3.l37 h52b h53 i.tab h510 i.fact512H
    G t L S z r B A K₁ K₂ hK
  exact hS.notChev3 (i.l520 G t L S z r B A K₁ K₂ h' hH)

end CFSG.OddStandard.SmallF3.Omega
