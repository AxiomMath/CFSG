module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.LocalAnalysis.OddStandard.GlueL34
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Suz
public import CFSG.LocalAnalysis.ComponentClassification.GSLitTripleBranch

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

theorem card_sylow_centralizer_eq_two_of_suz
    (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ g h : G, g * h ≠ h * g)
    (hK : Assembly.KProper Blueprint.Catalog G) (hU : ¬ OutcomeLocal.UOutcome G)
    {A : Subgroup G} (hA : IsStandardSubgroup A)
    (hSuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz)
    (S : Sylow 2 ↥(centralizer (A : Set G))) : Nat.card S = 2 := by
  have hstd := CFSG.IsStandardSubgroup.assembly hA
  have hS : OddStandard.StandardSetting G A :=
    ⟨inferInstance, hnonab, hK, CFSG.IsStandardSubgroup.standardComponentIsStandard hA⟩
  have hrow := (EvenSporadicStandard.HypOne.Suz.fullRowData_of_isSporadic hSuz).rowData
  have h7 : 7 ∣ Nat.card G := by
    have hdvd := OddStandard.GlueL34.card_quotient_center_dvd A
    obtain ⟨e⟩ := hSuz
    have hcard : Nat.card (↥A ⧸ center ↥A) = 448345497600 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Suz.card_Suz
    rw [hcard] at hdvd
    exact (by norm_num : 7 ∣ 448345497600).trans hdvd
  rcases StandardRecognition.standard_centralizer_rank_split hstd S with
    hrank | ⟨hcyc, -⟩ | ⟨n, hn, hSq, -⟩
  ·
    exact False.elim (hAS G A (OddStandard.GlueL34.rankTwoHyp hS hrank)
      (OddStandard.GlueL34.oddCore_eq_bot hS) hSuz)
  ·
    exact EvenSporadicStandard.Finkelstein77.card_sylow_eq_two_of_simple hnonab hstd
      S hcyc hrow.hypothesisOne hrow.rank h25
  ·
    rcases StandardRecognition.quaternion_standard_recognition hCIT hS.nonab hstd
      S hn hSq with hlie | hM11 | hM12
    · exact False.elim (hU (CFSG.ComponentClassification.GSLit.uOutcome_of_oddLieType hlie))
    · obtain ⟨e⟩ : Nonempty (G ≃* Blueprint.NativeSporadic.M11) := hM11
      have hG : Nat.card G = 7920 :=
        (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M11
      rw [hG] at h7
      omega
    · obtain ⟨e⟩ : Nonempty (G ≃* Blueprint.NativeSporadic.M12) := hM12
      have hG : Nat.card G = 95040 :=
        (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12
      rw [hG] at h7
      omega

end CFSG.ComponentClassification.GrSLit.L34Sec5S
