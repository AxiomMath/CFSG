module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXSpec6

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model
  CFSG.EvenSporadicStandard.HNRecog.TwoHSData

section Cert


theorem suborbitFacts_tableX :
    ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
      ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
        ∀ x : H, IsConj z x → TableXData a x b z₁ := by
  intro H _ E h a z b z₁ hf hd x hx
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ₀, -, hΨ₀⟩ := exists_labelled_iso_at_z h hf hd (IsConj.refl z)
  have hK : IsShapeK ↥(_root_.commutator ↥P1408 ⊓ Gx pZ) := by
    have hKe := map_K_eq Ψ₀ z
    rw [hΨ₀] at hKe
    have h1 := IsShapeK.of_mulEquiv
      (mapSubgroupMulEquiv Ψ₀ (_root_.commutator H ⊓ centralizer ({z} : Set H))) hf.K_shape
    rw [hKe] at h1
    exact h1
  obtain ⟨Ψ, hΨ, hΨx⟩ := exists_labelled_iso_at_z h hf hd hx
  have h1 := TableXData.congr pA_mem_center' hΨ.b_conj hΨ.z₁_conj (tableX_P hP hK)
  rw [← hΨx, ← hΨ.a_eq] at h1
  exact TableXData.of_map Ψ h1

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3
