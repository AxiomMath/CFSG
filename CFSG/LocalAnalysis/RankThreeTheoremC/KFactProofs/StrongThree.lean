module

public import CFSG.RankThree.PartTwo.Sec21.Item234
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.FrontierSeitz
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AutomizerMain
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Main
public import CFSG.LieType.SeitzGeneration.ConsumerEx
public import CFSG.HardMathSupport.Malle.SeitzCube.InnerExFrontier
public import CFSG.LieType.SeitzGeneration.ExcSeitzStatus
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1Case
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusU3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusReeG2
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Phi3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.E8Phi5
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Final
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.LieType.SeitzGeneration.OmegaF2.Plus
public import CFSG.LieType.SeitzGeneration.OmegaF2.Minus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open scoped commutatorElement

theorem gl83StronglyEmbeddedThreeSolvable_of_kFactStrongThreeSolv
    (h : CFSG.AGLEmbeddingD2.McLaughlin.KFactStrongThreeSolv) :
    CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable := by
  intro X _ _ hK M hM hrank H T _ hHM hHT
  have hKo : CFSG.Open.IsKGroup X := CFSG.KCore.KGroupAllSimple.kGroupNonab hK
  by_cases hab : ∀ a b : H ⧸ T, a * b = b * a
  ·
    letI : CommGroup (H ⧸ T) := { (inferInstance : Group (H ⧸ T)) with mul_comm := hab }
    have hp : (Nat.card (H ⧸ T)).Prime := IsSimpleGroup.prime_card (α := H ⧸ T)
    by_cases h3 : 3 ∣ Nat.card (H ⧸ T)
    · left
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
    · right
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  ·
    push Not at hab
    have hperf : ⁅(⊤ : Subgroup (H ⧸ T)), (⊤ : Subgroup (H ⧸ T))⁆ = (⊤ : Subgroup (H ⧸ T)) := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (H ⧸ T)) with h0 | h0
      · exfalso
        obtain ⟨a, b, hab⟩ := hab
        have hc : ⁅a, b⁆ ∈ commutator (H ⧸ T) := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hab hc
      · rw [← commutator_def]
        exact h0
    set Q : Subgroup H := CFSG.Quasithin.perfectCore (⊤ : Subgroup H) with hQ
    have hQmap : Q.map (QuotientGroup.mk' T) = ⊤ := by
      rw [hQ, CFSG.Quasithin.map_perfectCore, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective T)]
      exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf
    have hdvd : Nat.card (H ⧸ T) ∣ Nat.card Q := by
      have h1 := Subgroup.card_map_dvd (H := Q) (QuotientGroup.mk' T)
      rwa [hQmap, Subgroup.card_top] at h1
    have hQp : ⁅Q, Q⁆ = Q := CFSG.Quasithin.perfectCore_perfect _
    have hYM : Q.map H.subtype ≤ M := by
      rintro _ ⟨y, -, rfl⟩
      exact hHM y.2
    have hYperf : ⁅Q.map H.subtype, Q.map H.subtype⁆ = Q.map H.subtype := by
      rw [← Subgroup.map_commutator, hQp]
    have hYcard : Nat.card (Q.map H.subtype) = Nat.card Q :=
      Subgroup.card_map_of_injective H.subtype_injective
    have h3 := h X hKo M hM hrank (Q.map H.subtype) hYM hYperf
    right
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3'
    exact h3 (hYcard ▸ dvd_trans h3' hdvd)

section Holds


theorem gls3StronglyThreeEmbeddedPlus_holds : Gls3StronglyThreeEmbeddedPlus := by
  have hAniN :
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus :=
    CFSG.LieType.SeitzGeneration.seitzExcAnisotropicNotG2ThreePlus_of_yardsticks
      ⟨CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.seitzExcAnisotropicF4Class_three,
        CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicF4Class_six⟩
      ⟨CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE6Class_six,
        CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.seitzExcAnisotropicE8Class_five,
        CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE8Class_ten,
        CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE8Class_twelve⟩
      (CFSG.HardMathSupport.Seitz.TrialityEven.seitzExcAnisotropicTrialityEvenThree_of_leaves
        CFSG.HardMathSupport.Seitz.TrialityEven.trialityTwoThreePlanes_holds)
  have hOut : CFSG.LieType.SeitzGeneration.SeitzOuterLowN :=
    (CFSG.HardMathSupport.Malle.SeitzCube.innerEx_lowN_of_pairs_aniso
      CFSG.LieType.SeitzGeneration.subfieldPairSpF2_holds
      CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds
      (CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusChar2_of_F2
        CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusF2_holds)
      (CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusChar2_of_F2
        CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusF2_holds)
      hAniN CFSG.LieType.SeitzGeneration.seitzExcOuterNarrow_holds).2.2
  have hR1 : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 →
      CFSG.AGLEmbedding.IsRankOneLieIndex d.1 → Gls3PlusCase (.lie d) := by
    intro d h3 hd
    rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨m, hm⟩
    · exact gls3PlusCase_lie_rankOne_A1 q (by simpa [hq] using h3) d hq
    · exact gls3PlusCase_lie_rankOne_U3 q (by simpa [hq] using h3) d hq
    · exact gls3PlusCase_lie_reeG2 m d hm
  exact gls3StronglyThreeEmbeddedPlus_of_seitz
    (CFSG.LieType.SeitzGeneration.offCharGen_of_seitzEx
      (CFSG.HardMathSupport.Malle.SeitzCube.kFactSeitzRankTwoInnerEx_of_anisoN hAniN))
    hOut hR1

theorem kFactStrongThreeSolv_holds : CFSG.AGLEmbeddingD2.McLaughlin.KFactStrongThreeSolv :=
  kFactStrongThreeSolv_of_gls3 CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
      (gls3_of_plus gls3StronglyThreeEmbeddedPlus_holds)

theorem kFactStrongThreeAutomizer_holds :
    CFSG.AGLEmbeddingD2.McLaughlin.KFactStrongThreeAutomizer :=
  kFactStrongThreeAutomizer_of_gls3Plus gls3StronglyThreeEmbeddedPlus_holds

theorem gl83StronglyEmbeddedThreeSolvable_holds :
    CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable :=
  gl83StronglyEmbeddedThreeSolvable_of_kFactStrongThreeSolv kFactStrongThreeSolv_holds

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
