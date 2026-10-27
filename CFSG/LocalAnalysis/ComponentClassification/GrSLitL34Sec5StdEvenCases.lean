module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5StdEven
public import CFSG.LocalAnalysis.OddStandard.ChildL34
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank

public section

namespace CFSG.ComponentClassification.GSThmB

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard

theorem l34StandardEvenInput_of_cases
    (hRank : RankTwoL3FourStandard)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hOddLie : OddLieNoStandardL34) (hEven : L34CyclicEvenCenter) : L34StandardEvenInput := by
  intro G _ _ _ hnonab hK L hL h34 hev
  have hS : StandardSetting G L :=
    ⟨inferInstance, hnonab, hK, standardComponentIsStandard_of_cfsgStandard hL⟩
  have hstd := hS.standard
  have key : IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .ONan := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
    rcases StandardRecognition.standard_centralizer_rank_split hstd S with
      hrank | ⟨hcyc, -⟩ | ⟨n, hn, hSq, -⟩
    ·
      have hX : Subgroup.normalClosure (L : Set G) ≃* G :=
        (MulEquiv.subgroupCongr (GlueL34.normalClosure_eq_top hS)).trans Subgroup.topEquiv
      rcases hRank G L (GlueL34.rankTwoHyp hS hrank)
        (GlueL34.statedClassicalModel_of_lieModel_psl34 h34) (GlueL34.oddCore_eq_bot hS) with
        hSuz | ⟨-, hHe⟩
      · exact Or.inl (GlueL34.isSporadic_of_mulEquiv hX.symm hSuz)
      · exact Or.inr (Or.inl (GlueL34.isSporadic_of_mulEquiv hX.symm hHe))
    ·
      exact Or.inr (Or.inr (hEven G L hS h34 hev S hcyc))
    ·
      have hdvd : 20160 ∣ Nat.card G := by
        have h := GlueL34.card_quotient_center_dvd L
        rwa [GlueL34.card_eq_of_lieModel_psl34 h34] at h
      rcases StandardRecognition.quaternion_standard_recognition hCIT hS.nonab hstd S hn hSq
        with hlie | hM11 | hM12
      · exact (hOddLie G hlie L hstd h34).elim
      · obtain ⟨e⟩ : Nonempty (G ≃* NativeSporadic.M11) := hM11
        have hG : Nat.card G = 7920 :=
          (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M11
        rw [hG] at hdvd
        omega
      · obtain ⟨e⟩ : Nonempty (G ≃* NativeSporadic.M12) := hM12
        have hG : Nat.card G = 95040 :=
          (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12
        rw [hG] at hdvd
        omega
  exact key

end CFSG.ComponentClassification.GSThmB
