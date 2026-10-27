module

public import CFSG.HardMathSupport.Lang.AnisoE6.TwFinal
public import CFSG.HardMathSupport.Lang.AnisoE8.Final
public import CFSG.HardMathSupport.Lang.AnisoF4.FinalEven
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ResidualHandback
public import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.Closed
public import CFSG.HardMathSupport.Seitz.TrialityEven.Assembly
public import CFSG.HardMathSupport.Seitz.TrialityEven.TwoThree
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThreeAll
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicAssemblyV6
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeF4ThreeProved
public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
public import CFSG.LieType.SeitzGeneration.ExcParabolic
public import CFSG.LieType.SeitzGeneration.ExcSeitzWide
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Fields
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Twisted
public import CFSG.Yardstones.M0a200c08cf60.Definitions
public import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.Handback

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

section

open CFSG.HardMathSupport.Seitz CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
  CFSG.Yardstones.M0a200c08cf60 CFSG.RankThree.PartOne


theorem seitzExcAnisotropicNotG2ThreePlus_of_yardsticks
    (h4 : ExcAnisotropicF4Residuals) (h5 : ExcAnisotropicE6E8Residuals)
    (h6 : CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.SeitzExcAnisotropicTrialityEvenThree) :
    SeitzExcAnisotropicNotG2ThreePlus :=
  seitzExcAnisotropicNotG2ThreePlus_of_residualsV6
    { g2NineFive := seitzExcAnisotropicG2NineFive_proved
      g2Three := seitzExcAnisotropicG2ThreeMinus_proved
      trialityOdd := SeitzExcAnisotropicForAt.mono (fun _ _ hQ => hQ.2)
        TrialityOdd.Coordinator.seitzExcAnisotropicForAt_trialityOdd_proved
      trialityThree :=
        TrialityOdd.Coordinator.seitzExcAnisotropicTrialityThree_of_even h6
      f4Phi3 := h4.f4Phi3
      f4Phi4 := CFSG.HardMathSupport.Lang.AnisoF4.seitzExcAnisotropicF4Class_four
      f4Phi6 := h4.f4Phi6
      e6Phi6 := h5.e6Phi6
      e8Phi5 := h5.e8Phi5
      e8Phi8 := CFSG.HardMathSupport.Lang.AnisoE8.seitzExcAnisotropicE8Class_eight
      e8Phi10 := h5.e8Phi10
      e8Phi12 := h5.e8Phi12
      twE6Phi3 :=
        CFSG.HardMathSupport.Lang.AnisoE6.seitzExcAnisotropicTwistedE6Class_three_of_f4 h4.f4Phi3
      twE6Phi4 := CFSG.HardMathSupport.Lang.AnisoF4.seitzExcAnisotropicTwistedE6Class_four
      reeF4Three := seitzExcAnisotropicReeF4Three_holds }

theorem seitzExcAnisotropic_of_yardsticks
    (h4 : ExcAnisotropicF4Residuals) (h5 : ExcAnisotropicE6E8Residuals)
    (h6 : CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.SeitzExcAnisotropicTrialityEvenThree) :
    SeitzExcAnisotropic :=
  seitzExcAnisotropic_of_cover
    G2Anisotropic.ExceptionsTransport.seitzExcAnisotropicG2ThreePlus_proved
    (seitzExcAnisotropicNotG2ThreePlus_of_yardsticks h4 h5 h6)

end

section

open CFSG.Yardstones.M0a200c08cf60 CFSG.RankThree.PartOne


theorem seitzExcOuterNarrow_of_yardstick (h : ExcOuterLeOneResiduals) : SeitzExcOuterNarrow :=
  seitzExcOuterNarrow_of_residualsV5
    { g2OddPower :=
        CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.seitzExcOuterNarrowG2OddPower_proved
      g2Three := CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.seitzExcOuterNarrowG2Three_proved
      trialityOdd := HardMathSupport.Seitz.TrialityOdd.seitzExcOuterNarrowTrialityOdd_of_pair
          HardMathSupport.Seitz.TrialityOdd.subfieldPairD4Odd_proof
      trialityThree :=
        CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.seitzExcOuterNarrowTrialityThree_proved
      f4EqTwo := CFSG.AGLEmbedding.SeitzEqTwo.seitzExcOuterNarrowF4EqTwo_holds
      f4LeOne := h.f4LeOne
      e6EqTwo := CFSG.AGLEmbedding.SeitzEqTwo.seitzExcOuterNarrowE6EqTwo_holds
      e6LeOne := h.e6LeOne
      e7EqTwo := CFSG.AGLEmbedding.SeitzEqTwo.seitzExcOuterNarrowE7EqTwo_holds
      e7LeOne := h.e7LeOne
      e8EqTwo := CFSG.AGLEmbedding.SeitzEqTwo.seitzExcOuterNarrowE8EqTwo_holds
      e8LeOne := h.e8LeOne
      twistedE6EqTwo := CFSG.AGLEmbedding.SeitzEqTwo.seitzExcOuterNarrowTwistedE6EqTwo_holds
      twistedE6LeOne := h.twistedE6LeOne
      reeG2 := CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.seitzExcOuterNarrowReeG2_of_pair
        CFSG.LocalAnalysis.SubfieldPairReeG2.subfieldPairReeG2_of_pieces
      reeF4Three := seitzExcOuterNarrowReeF4Three_holds }

end

theorem kFactSeitzRankTwo_of_regimes
    (hO : OrthogonalOddPlanes) (hP : OrthogonalPlusPlanes) (hM : OrthogonalMinusPlanes)
    (hN : SeitzInnerClassicalNonab) (h3c : SeitzInnerThreeClassical) (hoc : SeitzOuterClassical)
    (hPar : SeitzExcParabolic) (hAni : SeitzExcAnisotropic)
    (hH5 : SeitzExcHighFive) (hH3 : SeitzExcHighThree)
    (hNar : SeitzExcOuterNarrow) (hW5 : SeitzExcOuterWideFive) (hW3 : SeitzExcOuterWideThree) :
    KFactSeitzRankTwo :=
  kFactSeitzRankTwo_of_remaining_leaves hO hP hM hN
    (seitzInnerExceptionalFive_of_regimes hPar hAni hH5)
    (seitzInnerThree_of_regimes h3c (seitzInnerThreeExceptional_of_regimes hPar hAni hH3))
    (kFactSeitzRankTwoOuter_of_regimes hoc (seitzOuterExceptional_of_narrow_wide hNar hW5 hW3))

section

open CFSG.Yardstones.M0a200c08cf60


theorem seitzExcOuterNarrow_holds : SeitzExcOuterNarrow :=
  seitzExcOuterNarrow_of_yardstick
    (let h := ExcOuterLeOne.excOuterLeOne_fields
     ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)

theorem kFactSeitzRankTwo_of_exceptional_gaps
    (hO : OrthogonalOddPlanes) (hP : OrthogonalPlusPlanes) (hM : OrthogonalMinusPlanes)
    (hN : SeitzInnerClassicalNonab) (h3c : SeitzInnerThreeClassical) (hoc : SeitzOuterClassical)
    (h4 : ExcAnisotropicF4Residuals) (h5 : ExcAnisotropicE6E8Residuals)
    (hH5 : SeitzExcHighForAt IsTopIndex PrimeRange.geFive)
    (hH3 : SeitzExcHighForAt IsTopIndex PrimeRange.three)
    (hW3 : SeitzExcOuterWideThreeFamilies) : KFactSeitzRankTwo :=
  kFactSeitzRankTwo_of_regimes hO hP hM hN h3c hoc seitzExcParabolic
    (seitzExcAnisotropic_of_yardsticks h4 h5
      (CFSG.HardMathSupport.Seitz.TrialityEven.seitzExcAnisotropicTrialityEvenThree_of_leaves
        CFSG.HardMathSupport.Seitz.TrialityEven.trialityTwoThreePlanes_holds))
    (seitzExcHighFive_of_top hH5)
    (seitzExcHighThree_of_top hH3) seitzExcOuterNarrow_holds seitzExcOuterWideFive_holds
    hW3.toWideThree

end

end CFSG.LieType.SeitzGeneration
