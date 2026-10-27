module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NTwoA
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NoSP
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3In
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CycRest

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoRest3 (G : Type) [Group G] [Finite G] : Prop := D1CaseTwoNormalFormRest3 G

theorem d1CaseTwoRest3_of_caseTwo3 (h : D1CaseTwo3 G) : D1CaseTwoRest3 G :=
  fun p P M H R Rbar hd _ _ _ _ _ _ _ _ _ _ _ => h p P M H R Rbar hd.cfg hd.cyclic

structure D1CaseTwoKFacts3 (G : Type) [Group G] [Finite G] : Prop where
  out : KFactOutCyclic
  seitzCyc : KFactSeitzCyc
  caseTwoLocal : KFactCaseTwoLocal
  inv : D1CaseTwoInv3 G
  schreier : KFactCatalogSchreier
  sylow : KFactCaseTwoSylow
  noTwo : KFactCaseTwoNoTwo
  centerFive : KFactCenterFive
  alphaThree : KFactCaseTwoAlphaThree
  outerSylow : KFactOuterSylowInner
  eightFour : Asc81bEightFour
  eightFive : Asc81bEightFive
  eightSix : Asc81bEightSix
  nineThree : Asc81bNineThree
  noXBlock : D1NoXBlock
  localCGT : AschbacherLocalCGTBlock
  twoGenInner : KFactTwoGenInner
  parabolicPrime : KFactParabolicPrime
  transvectionPrime : CitedBlockTransvectionPrime
  altSevenPrime : KFactBlockAltSevenPrime
  parabolicThree : KFactParabolicThree
  threeTransvection : CitedBlockThreeTransvection
  threeAltSeven : KFactBlockThreeAltSeven
  autPrimeInner : KFactBlockAutPrimeInner
  outPrime : KFactBlockOutPrime
  toralThree : CitedBlockToralThree
  toralThreeAut : CitedBlockToralThreeAut
  toralCycAut : CitedBlockToralCycAut
  toralThreeCyc : CitedBlockToralThreeCyc

theorem d1CaseTwoPosZero_of_noSP3 (h : D1CaseTwoPosZeroNoSP G) : D1CaseTwoPosZero G :=
  fun p P M H R Rbar hd hU h0 => h p P M H R Rbar hd (d1CaseTwoNoSP_of_config3 hd.cfg) hU h0

theorem d1CaseTwoNTwoARes_of_noSP3 (h : D1CaseTwoNTwoAResNoSP G) : D1CaseTwoNTwoARes G :=
  fun p P M H R Rbar hd hU L₁ L₂ h1 h2 h3 h4 h5 h6 =>
    h p P M H R Rbar hd (d1CaseTwoNoSP_of_config3 hd.cfg) hU L₁ L₂ h1 h2 h3 h4 h5 h6

theorem d1CaseTwoZZThree_of_noSP3 (h : D1CaseTwoZZThreeNoSP G) : D1CaseTwoZZThree G :=
  fun P M H R Rbar hd hU L₁ h1 h2 h3 h4 z h5 h6 h7 =>
    h P M H R Rbar hd (d1CaseTwoNoSP_of_config3 hd.cfg) hU L₁ h1 h2 h3 h4 z h5 h6 h7

theorem d1CaseTwo3_of_residues3 (hK : D1CaseTwoKFacts3 G) (hC : D1CaseTwoComp3 G)
    (hrest : D1CaseTwoRest3 G) : D1CaseTwo3 G := by
  have hNFa : D1CaseTwoNormalFormTwoA G :=
    d1CaseTwoNormalFormTwoA_of_rest3 hK.out hK.seitzCyc hK.caseTwoLocal hK.inv hK.schreier
      hK.sylow hK.eightFour hK.eightFive hK.eightSix hK.nineThree hK.noXBlock hK.autPrimeInner
      hK.parabolicPrime hK.transvectionPrime hK.altSevenPrime hK.parabolicThree
      hK.threeTransvection hK.threeAltSeven hK.outPrime hK.toralThree hK.toralThreeAut
      hK.toralCycAut hK.toralThreeCyc hrest
  have hNF : D1CaseTwoNormalForm G :=
    d1CaseTwoNormalForm_of_twoA hK.out hK.seitzCyc hK.caseTwoLocal hK.schreier hK.eightFour
      hK.eightFive hK.eightSix hK.nineThree hK.noXBlock hK.parabolicPrime hK.transvectionPrime
      hK.altSevenPrime hK.parabolicThree hK.threeTransvection hK.threeAltSeven hK.autPrimeInner
      hNFa
  have hIn0 : D1CaseTwoPosZeroInThree G :=
    d1CaseTwoPosZeroInThree_of hK.out hK.seitzCyc hK.sylow hK.schreier hK.alphaThree
  have hInr : D1CaseTwoNTwoAResInThree G :=
    d1CaseTwoNTwoAResInThree_of hK.out hK.seitzCyc hK.sylow hK.schreier hK.alphaThree
  have hInz : D1CaseTwoZZThreeIn G :=
    d1CaseTwoZZThreeIn_of hK.out hK.seitzCyc hK.sylow hK.schreier hK.alphaThree
  have hz3 : D1CaseTwoZZThreeNoSP G :=
    d1CaseTwoZZThreeNoSP_of_kFacts hK.out hK.seitzCyc hK.caseTwoLocal hK.inv hK.schreier hK.sylow
      hK.noTwo
      (d1CaseTwoZZThreeEV_of_nf hK.out hK.seitzCyc hK.caseTwoLocal hK.inv hK.schreier hK.sylow
        hK.noTwo hK.outerSylow hC hNF) hInz
  have h0 : D1CaseTwoPosZeroNoSP G :=
    d1CaseTwoPosZeroNoSP_of_residues hK.out hK.seitzCyc hK.caseTwoLocal hK.inv hK.schreier
      hK.sylow hK.noTwo hK.centerFive
      (d1CaseTwoPosZeroEV_of_nf hK.out hK.seitzCyc hK.caseTwoLocal hK.inv hK.schreier hK.sylow
        hK.noTwo hK.outerSylow hC hNF) hIn0
  have hres2 : D1CaseTwoNTwoAResNoSP G :=
    d1CaseTwoNTwoAResNoSP_of_residues hK.out hK.seitzCyc hK.caseTwoLocal hK.inv hK.schreier
      hK.sylow hK.noTwo hK.centerFive
      (d1CaseTwoNTwoAResEV_of_nf hK.out hK.seitzCyc hK.caseTwoLocal hK.inv hK.schreier hK.sylow
        hK.noTwo hK.outerSylow hC hNF) hInr
  have h2 : D1CaseTwoRankThree G :=
    d1CaseTwoRankThree_of_res hK.out hC hK.seitzCyc hK.caseTwoLocal hK.inv hK.schreier
      hK.eightFour hK.eightFive hK.eightSix hK.nineThree hK.noXBlock hK.localCGT hK.twoGenInner
      hK.parabolicPrime hK.transvectionPrime hK.altSevenPrime (d1CaseTwoPosZero_of_noSP3 h0)
      (d1CaseTwoNTwoARes_of_noSP3 hres2) (d1CaseTwoZZThree_of_noSP3 hz3)
  exact d1CaseTwo3_of_data3 hC.central h2

end CFSG.LocalAnalysis.RankThreeTheoremC
