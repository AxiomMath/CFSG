module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab4Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableDataMap

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

section Cert


theorem suborbitFacts_tableIV :
    ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
      ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
        ∀ y : H, IsConj b y → TableIVData a z b z₁ y := by
  intro H _ E h a z b z₁ hf hd y hy
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ, hΨ, hΨy⟩ := exists_labelled_iso_at_b h hf hd hy
  have h1 := TableIVData.congr pA_mem_center' hΨ.z_conj hΨ.b_conj hΨ.z₁_conj (tableIV_P hP)
  rw [← hΨ.a_eq, ← hΨy] at h1
  exact TableIVData.of_map Ψ h1

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3
