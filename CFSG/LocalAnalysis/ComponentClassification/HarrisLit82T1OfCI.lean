module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Open
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XFacts
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Open
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFour
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QPSL
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QPSU
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSpFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXTw
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QD4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QRee
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226S
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQ
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LS8Spin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Wire
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3U4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Sp4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3D4Row
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDRowM
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDRowP
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LE7Inv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35EMain
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxH35Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFinal

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

section Certified


theorem harris82Theorem1KProper_of_ci (hCI : GSLit.ClassicalInvolutionInput) :
    Harris82Theorem1KProper := by
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have hGLS : CatLeaf.GLS3OddLieAutComponentsInput := GrSLit.gls3OddLieAutComponentsInput_holds
  have hES : Harris81Lemma35IdentEvenSporFact :=
    harris81Lemma35IdentEvenSporFact_of_spor hGLS hGA
      SolMax.H35.harris81Lemma35IdentSporFact_holds
  have hId35 : Harris81Lemma35IdentFact :=
    harris81Lemma35IdentFact_of_nonAlt hCI
      (harris81Lemma35IdentNonAltFact_of_resid
        Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
        EvenSporadicStandard.centralTwoBound
        (harris81Lemma35IdentResidFact_of_cover hGLS hGA
          (harris81Lemma35IdentCoverFact_of_four
            (harris81Lemma35IdentFourCoverFact_of_evenSpor hGA hES))))
  have hFE7 : P51Q.FamF .E7 := P51Q.famF_E7
  have hFTE6 : P51Q.FamF .twistedE6 := P51Q.famF_twistedE6
  have h51 : Harris82Lemma51Quat :=
    P51Q.harris82Lemma51Quat_of_famF P51Q.famF_psl P51Q.famF_psu P51Q.famF_PSp
      P51Q.famF_POmegaOdd P51Q.famF_POmegaPlus P51Q.famF_POmegaMinus P51Q.famF_G2
      P51Q.famF_F4 P51Q.famF_E6 hFE7 P51Q.famF_E8 hFTE6 P51Q.famF_trialityD4
      P51Q.famF_twistedG2
  have h51E4 : Harris82Lemma51E4 :=
    P51Q.harris82Lemma51E4_of_famF P51Q.famF_psl P51Q.famF_psu P51Q.famF_PSp
      P51Q.famF_POmegaOdd P51Q.famF_POmegaPlus P51Q.famF_POmegaMinus P51Q.famF_G2
      P51Q.famF_F4 P51Q.famF_E6 hFE7 P51Q.famF_E8 hFTE6 P51Q.famF_trialityD4
      P51Q.famF_twistedG2
  have hPSL4 : P58b3.Harris82Lemma58bThreeRowAt .PSL 4 1 :=
    P58b3.harris82Lemma58bThreeRowAt_PSL_four
  have hPSU4 : P58b3.Harris82Lemma58bThreeRowAt .PSU 4 1 :=
    P58b3.harris82Lemma58bThreeRowAt_PSU_four
  have hPSp2 : P58b3.Harris82Lemma58bThreeRowAt .PSp 2 1 :=
    P58b3.harris82Lemma58bThreeRowAt_PSp_two
  have hPSU : ∀ n : ℕ, Even n → 6 ≤ n → P58b3.Harris82Lemma58bThreeRowAt .PSU n 1 :=
    fun n _ h6 => by
      intro G _ _ z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ K hL₁ hL₂ hz₁L hz₂L he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z hm
      exact harris82Lemma58bThreeRow_PSU_of_six_le h51E4 h6 G z₁ z₂ hz₁ hz₂ hne hc L₁
        L₂ K hL₁ hL₂ hz₁L hz₂L he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z 1 hm
  have hPlus4 : P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus 4 1 :=
    harris82Lemma58bThreeRowAt_POmegaPlus_four
  have hMinus4 : P58b3.Harris82Lemma58bThreeRowAt .POmegaMinus 4 1 :=
    harris82Lemma58bThreeRowAt_POmegaMinus_of_four_le
      TBLit.griessMultipliersAllModels_holds le_rfl
  have hPlusE : ∀ n : ℕ, Even n → 4 ≤ n → P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus n 1 :=
    fun n _ hn => by
      rcases Nat.lt_or_ge n 5 with h | h
      · obtain rfl : n = 4 := by omega
        exact hPlus4
      · exact harris82Lemma58bThreeRowAt_POmegaPlus_of_five_le h
  have hPlus : ∀ n : ℕ, 4 ≤ n → P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus n 1 :=
    fun n hn => by
      rcases Nat.even_or_odd n with he | ho
      · exact hPlusE n he hn
      · exact harris82Lemma58bThreeRowAt_POmegaPlus_one
          TBLit.griessMultipliersAllModels_holds (by obtain ⟨k, rfl⟩ := ho; omega) ho
  have hMinus : ∀ n : ℕ, 4 ≤ n → P58b3.Harris82Lemma58bThreeRowAt .POmegaMinus n 1 :=
    fun n hn => by
      rcases Nat.lt_or_ge n 5 with h | h
      · obtain rfl : n = 4 := by omega
        exact hMinus4
      · exact harris82Lemma58bThreeRowAt_POmegaMinus_one
          TBLit.griessMultipliersAllModels_holds h
  have hE7 : P58b3.Harris82Lemma58bThreeRowAt .E7 0 1 :=
    harris82Lemma58bThreeRowAt_E7_of_noKlein P58b3L.e7ThreeNoKlein_holds
  have h58 : Harris82Lemma58bThree :=
    harris82Lemma58bThree_of_rowsAt h51E4 hPSL4 hPSU4 hPSp2 hPSU hPlus hMinus hE7
  have hOut : Harris82OutQuatThree :=
    F3FG.harris82OutQuatThree_of_orth F3FG.harris82OutQuatThreeOrth_holds
  have hD4 : F3FG.FourGroupResidualStepD4 :=
    F3FG.fourGroupResidualStepD4_of_inputs spin8CentreFixedOutAbelian
      harris82Lemma413Three_holds harris82ThetaBalanceThree_holds
  have h4 : Harris82FourGroupThree :=
    F3FG.harris82FourGroupThree_of_inputs hCI (F3FG.knownRowThree_holds hCI h51)
      (harris82Lemma226Three_of_solvable harris82Lemma226ThreeSolvable_holds)
      (F3FG.fourGroupResidualStep_of_outQuat hOut hD4 harris82ThetaBalanceThree_holds)
  exact harris82Theorem1KProper_of_open hCI hId35 (harris82Theorem1FieldThree_of_open h4 h58)
    (S74.solomon74SpinSevenAsUsed_of S74.lemma38_holds S74.f1_holds S74.f2b_holds
        (S74.spinFactsAll_of S74.f1_holds S74.f2b_holds S74.f4_holds S74.a1_holds S74.a2_holds
            S74.a3_holds S74.a4_holds))

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
