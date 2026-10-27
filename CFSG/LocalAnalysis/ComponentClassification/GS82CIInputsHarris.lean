module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Open
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Open
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XFacts
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFour
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226S
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQ
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QPSL
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QPSU
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSpFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXTw
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QD4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QRee
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Wire
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3U4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Sp4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3D4Row
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDRowP
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDRowM
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LE7Inv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LS8Spin
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35EMain
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxH35Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFinal

public section

namespace CFSG.ComponentClassification.GSThmB

theorem harris82Theorem1KProper_of_ci
    (hCI : GSLit.ClassicalInvolutionInput) :
    HarrisLit.Harris82Theorem1KProper := by
  have hFE7 : HarrisLit.T1.P51Q.FamF .E7 := HarrisLit.T1.P51Q.famF_E7
  have hFTE6 : HarrisLit.T1.P51Q.FamF .twistedE6 := HarrisLit.T1.P51Q.famF_twistedE6
  have h51 : HarrisLit.T1.Harris82Lemma51Quat :=
    HarrisLit.T1.P51Q.harris82Lemma51Quat_of_famF HarrisLit.T1.P51Q.famF_psl
      HarrisLit.T1.P51Q.famF_psu HarrisLit.T1.P51Q.famF_PSp HarrisLit.T1.P51Q.famF_POmegaOdd
      HarrisLit.T1.P51Q.famF_POmegaPlus HarrisLit.T1.P51Q.famF_POmegaMinus HarrisLit.T1.P51Q.famF_G2
      HarrisLit.T1.P51Q.famF_F4 HarrisLit.T1.P51Q.famF_E6 hFE7 HarrisLit.T1.P51Q.famF_E8 hFTE6
      HarrisLit.T1.P51Q.famF_trialityD4 HarrisLit.T1.P51Q.famF_twistedG2
  have h51E4 : HarrisLit.T1.Harris82Lemma51E4 :=
    HarrisLit.T1.P51Q.harris82Lemma51E4_of_famF HarrisLit.T1.P51Q.famF_psl
      HarrisLit.T1.P51Q.famF_psu HarrisLit.T1.P51Q.famF_PSp HarrisLit.T1.P51Q.famF_POmegaOdd
      HarrisLit.T1.P51Q.famF_POmegaPlus HarrisLit.T1.P51Q.famF_POmegaMinus HarrisLit.T1.P51Q.famF_G2
      HarrisLit.T1.P51Q.famF_F4 HarrisLit.T1.P51Q.famF_E6 hFE7 HarrisLit.T1.P51Q.famF_E8 hFTE6
      HarrisLit.T1.P51Q.famF_trialityD4 HarrisLit.T1.P51Q.famF_twistedG2
  have hPSU : ∀ n : ℕ, Even n → 6 ≤ n →
      HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .PSU n 1 :=
    fun n _ h6 => by
      intro G _ _ z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ K hL₁ hL₂ hz₁L hz₂L he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z hm
      exact HarrisLit.T1.harris82Lemma58bThreeRow_PSU_of_six_le h51E4 h6 G z₁ z₂ hz₁ hz₂ hne hc L₁
        L₂ K hL₁ hL₂ hz₁L hz₂L he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z 1 hm
  have hPlus : ∀ n : ℕ, 4 ≤ n →
      HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus n 1 :=
    fun n hn => by
      rcases Nat.lt_or_ge n 5 with h | h
      · obtain rfl : n = 4 := by omega
        exact HarrisLit.T1.harris82Lemma58bThreeRowAt_POmegaPlus_four
      · exact HarrisLit.T1.harris82Lemma58bThreeRowAt_POmegaPlus_of_five_le h
  have hMinus : ∀ n : ℕ, 4 ≤ n →
      HarrisLit.T1.P58b3.Harris82Lemma58bThreeRowAt .POmegaMinus n 1 :=
    fun _ hn => HarrisLit.T1.harris82Lemma58bThreeRowAt_POmegaMinus_of_four_le
      TBLit.griessMultipliersAllModels_holds hn
  have h58 : HarrisLit.T1.Harris82Lemma58bThree :=
    HarrisLit.T1.harris82Lemma58bThree_of_rowsAt h51E4
      HarrisLit.T1.P58b3.harris82Lemma58bThreeRowAt_PSL_four
      HarrisLit.T1.P58b3.harris82Lemma58bThreeRowAt_PSU_four
      HarrisLit.T1.P58b3.harris82Lemma58bThreeRowAt_PSp_two hPSU hPlus hMinus
      (HarrisLit.T1.harris82Lemma58bThreeRowAt_E7_of_noKlein
        HarrisLit.T1.P58b3L.e7ThreeNoKlein_holds)
  have hD4 : HarrisLit.T1.F3FG.FourGroupResidualStepD4 :=
    HarrisLit.T1.F3FG.fourGroupResidualStepD4_of_inputs HarrisLit.T1.spin8CentreFixedOutAbelian
      HarrisLit.T1.harris82Lemma413Three_holds HarrisLit.T1.harris82ThetaBalanceThree_holds
  have h4 : HarrisLit.T1.Harris82FourGroupThree :=
    HarrisLit.T1.F3FG.harris82FourGroupThree_of_inputs hCI
      (HarrisLit.T1.F3FG.knownRowThree_holds hCI h51)
      (HarrisLit.T1.harris82Lemma226Three_of_solvable
        HarrisLit.T1.harris82Lemma226ThreeSolvable_holds)
      (HarrisLit.T1.F3FG.fourGroupResidualStep_of_outQuat
        (HarrisLit.T1.F3FG.harris82OutQuatThree_of_orth
          HarrisLit.T1.F3FG.harris82OutQuatThreeOrth_holds)
        hD4 HarrisLit.T1.harris82ThetaBalanceThree_holds)
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have hGLS : CatLeaf.GLS3OddLieAutComponentsInput := GrSLit.gls3OddLieAutComponentsInput_holds
  have hES : HarrisLit.Harris81Lemma35IdentEvenSporFact :=
    HarrisLit.harris81Lemma35IdentEvenSporFact_of_spor hGLS hGA
      SolMax.H35.harris81Lemma35IdentSporFact_holds
  have hId35 : HarrisLit.Harris81Lemma35IdentFact :=
    HarrisLit.harris81Lemma35IdentFact_of_nonAlt hCI
      (HarrisLit.harris81Lemma35IdentNonAltFact_of_resid
        Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
        EvenSporadicStandard.centralTwoBound
        (HarrisLit.harris81Lemma35IdentResidFact_of_cover hGLS hGA
          (HarrisLit.harris81Lemma35IdentCoverFact_of_four
            (HarrisLit.harris81Lemma35IdentFourCoverFact_of_evenSpor hGA hES))))
  exact HarrisLit.T1.harris82Theorem1KProper_of_open hCI hId35
    (HarrisLit.T1.harris82Theorem1FieldThree_of_open h4 h58)
    (HarrisLit.T1.S74.solomon74SpinSevenAsUsed_of HarrisLit.T1.S74.lemma38_holds
        HarrisLit.T1.S74.f1_holds HarrisLit.T1.S74.f2b_holds
        (HarrisLit.T1.S74.spinFactsAll_of HarrisLit.T1.S74.f1_holds HarrisLit.T1.S74.f2b_holds
            HarrisLit.T1.S74.f4_holds HarrisLit.T1.S74.a1_holds HarrisLit.T1.S74.a2_holds
            HarrisLit.T1.S74.a3_holds HarrisLit.T1.S74.a4_holds))

end CFSG.ComponentClassification.GSThmB
