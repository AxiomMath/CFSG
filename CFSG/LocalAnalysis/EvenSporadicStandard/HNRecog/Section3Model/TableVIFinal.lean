module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableDataMap

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

section Cert


theorem suborbitFacts_tableVI :
    ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
      ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
        ∀ y : H, IsConj (a * z) y → TableVIData a z b z₁ y := by
  intro H _ E h a z b z₁ hf hd y hy
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ, hΨ, hΨy⟩ := exists_labelled_iso_at_az h hf hd hy
  have h1 := TableVIData.congr pA_mem_center' hΨ.z_conj hΨ.b_conj hΨ.z₁_conj (tableVI_P hP)
  rw [← hΨy, ← hΨ.a_eq] at h1
  exact TableVIData.of_map Ψ h1

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3
