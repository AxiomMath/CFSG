module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFElevenK
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverAssembly
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig27
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol78Bridge
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9T
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineJ
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapNarrow
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitCycOddJ
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Apps

public section

namespace CFSG.ComponentClassification.SolMax

theorem solomonAlternatingOddInput_of_leaves_cycOddJ
    (hRank2 : RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hCyc : SolAltLit.AltStdCyclicOddJ) (h13 : Sol76T13.SolomonThm13Simple)
    (hsig : SolAltLit.SignalizerTrivialityInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) : SolAltLit.SolomonAlternatingOddInput :=
  SolAltLit.solaltlit_odd_of_sol78_inputs_cycOddJ hRank2 hCIT hCyc
    (Sol78.maximalAltComponent_of_thm13_of_maximality h13
      (maximalityLemmaInput_of_inputs hPump hN1)
      Alternating.Multipliers.schurAlternatingMultiplierInput)
    hsig Alternating.Multipliers.schurAlternatingMultiplierInput

theorem solomonAlternatingOddInput_of_signalizer_cycOddJ
    (hRank2 : RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hCyc : SolAltLit.AltStdCyclicOddJ) (h13 : Sol76T13.SolomonThm13Simple)
    (hsig : SolAltLit.SignalizerTrivialityInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hSig : GSThmB.SolomonSignalizerInput) : SolAltLit.SolomonAlternatingOddInput :=
  solomonAlternatingOddInput_of_leaves_cycOddJ hRank2 hCIT hCyc h13 hsig hPump
    (twoGroupAltCoverExclusion_of_inputs hSig
      Alternating.Multipliers.schurAlternatingMultiplierInput hPump)

theorem solomonAlternatingOddInput_of_open_five_cases_alt_cycOddJ
    (hRank2 : RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hCyc : SolAltLit.AltStdCyclicOddJ) (h13 : Sol76T13.SolomonThm13Simple)
    (hPump : Sol78.AlternatingPumpUpInput) (hSig : GSThmB.SolomonSignalizerInput)
    (hR1 : SignalizerSwapMemberNarrowInput) (hTB : SignalizerFivePumpTBInput)
    (hF3 : SignalizerFivePumpThreeFixInput) (hFL2 : SignalizerFivePumpLTwoInput)
    (hFHe : SignalizerFivePumpHeldInput) (hFL34 : SignalizerFivePumpLThreeFourInput)
    (hHe : SignalizerHeldPumpExclusionInput) (h2 : SignalizerCaseTwoFinishInput)
    (hAlt : SignalizerCaseOneConjugateOutsideAltInput)
    (hFC : SignalizerNineFusionCountInput) :
    SolAltLit.SolomonAlternatingOddInput :=
  have hbal : Sol78.BalanceTwoComponentInput := Sol78.balanceTwoComponentInput_holds
  have hSch : SolAltLit.SchurAlternatingMultiplierInput :=
    Alternating.Multipliers.schurAlternatingMultiplierInput
  have hN1 : TwoGroupAltCoverExclusion := twoGroupAltCoverExclusion_of_inputs hSig hSch hPump
  have hML : Sol78.MaximalityLemmaInput := maximalityLemmaInput_of_signalizer hPump hSig
  have h9s : SignalizerSmallDegreeNineInput :=
    signalizerSmallDegreeNineInput_of_fivePump hbal hPump hN1
      (signalizerFivePumpBalanceInput_of_exact hbal
        (signalizerFivePumpExactInput_of_cases hbal hTB hF3 hFL2 hFHe hFL34))
  have hsmall : SignalizerSmallDegreeInput :=
    signalizerSmallDegreeInput_of_nine hbal hPump hN1 hHe h9s
  have h33 : Sol78.BalanceLemmaInput := balanceLemmaInput_of_smallDegree hbal hPump hN1 hsmall
  have h35 : SignalizerLemma35 := signalizerLemma35_of_smallDegree hbal hPump hN1 hsmall
  have h9 : SignalizerNineInput :=
    signalizerNineInput_of_strongClosure h33 h35 h13 hML hSch stronglyClosedResidualInput_holds
      (signalizerNineStrongClosureInput_of_conjugate
        (signalizerNineConjugateInput_of_fusionCount h33 h35 h13 hML hSch hFC))
  have hA : SignalizerClaimASmallInput :=
    signalizerClaimASmallInput_of_nine h33 h35 hPump hN1
      (signalizerClaimANineInput_of_inputs h33 h35 hPump hN1)
  solomonAlternatingOddInput_of_signalizer_cycOddJ hRank2 hCIT hCyc h13
    (signalizerTrivialityInput_of_residues_alt_eleven
      (Sol78.maximalAltComponent_of_thm13_of_maximality h13 hML hSch) hbal hPump hN1 hsmall h13
      hML hSch (swapAltExclusion_of_narrow h33 h35 h13 hML hSch hR1)
      stronglyClosedResidualInput_holds hA h2
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate hAlt h9)
    hPump hSig

end CFSG.ComponentClassification.SolMax
