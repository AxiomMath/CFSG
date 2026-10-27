module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5DSpecB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5ModelA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5ModelB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Norm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YSpecD

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.Section3

section Cert


theorem simple2S5_core :
    ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
      ∀ S : Subgroup H, IsSimpleGroup ↥S → ∀ t : ↥S, t ^ 2 = 1 → t ≠ 1 →
        IsNonsplitDoubleCoverOfS5 ↥(Subgroup.centralizer ({t} : Set ↥S)) → IsShapeU35 ↥S := by
  intro H _ E hE S hS t ht2 ht1 hY
  obtain ⟨S₁, t₁, hgood, ⟨e₁⟩⟩ := exists_good_of_simple hE ht2 ht1 hY
  have hΛ : HSCtx := hsCtx_of_isHSCover hE.toIsHSCover
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 hΛ
  obtain ⟨S₃, k, hk, hgood₃, hSP, haS, hdvd, hY₃, ⟨e₂⟩⟩ :=
    exists_normalized hΛ (yFacts_of_cert hP) hgood
  have hA1 : elemA ≠ 1 := fun h => by
    have h2 := twoHSBasic_spec.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨hk0, hSyl, h, hhS, hh1, hh2⟩ :=
    exists_h_of_tmuFacts tmuFacts_of_cert hgood₃ hk hY₃
  subst hk0
  obtain ⟨p, hp⟩ := eq_stab_of_dFacts hP tmuFacts_of_cert.k0 (dFacts_of_cert hP) hgood₃ hSP hA1
    haS hdvd hY₃ hSyl hhS hh1 hh2
  obtain ⟨e₃⟩ := nonempty_mulEquiv_u0_of_eq_stab hp
  obtain ⟨f⟩ := isShapeU35_u0 hP
  exact ⟨(e₁.trans (e₂.trans e₃)).trans f⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
