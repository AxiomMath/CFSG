module

public import CFSG.ClassicalInvolution.Asc77.AscT7V6
public import CFSG.ClassicalInvolution.Asc77.AscT7JCent
import CFSG.ClassicalInvolution.Asc77.AscT7S22Sigma

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7V

set_option linter.unusedSectionVars false

section Wyl

variable {p f : ℕ} [Fact p.Prime]

theorem c22_4_of_wyl (hR : Hyp22SettingWyl p f) : C22_4 p f :=
  fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h W hW => hR G Ω K K' K₃ z u₁ u₂ u₃ h.setting W hW

theorem hyp22Fuse_of_wyl (hR : Hyp22SettingWyl p f) : Hyp22Fuse p f :=
  hyp22Fuse_of_c22_4 (c22_4_of_wyl hR)

theorem hyp22ZStarCu_of_wyl (hR : Hyp22SettingWyl p f) : Hyp22ZStarCu p f :=
  fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h W hW hμ =>
    absurd (hR G Ω K K' K₃ z u₁ u₂ u₃ h.setting W hW) hμ

@[expose] def Hyp22SigmaNe (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      dComp Ω K ≠ dstarComp Ω K

theorem hyp22SettingWyl_of_sigmaNe (hσ : Hyp22SigmaNe p f) : Hyp22SettingWyl p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h W hW
  have hP : PartIHyp p f Ω := ⟨h.stand.odd, h.stand.five, h.stand.hyp, h.stand.aEmpty⟩
  have hnc : ¬ DbarConnected Ω W :=
    thompsonGraphAll G Ω hP h.stand.mem (hσ G Ω K K' K₃ z u₁ u₂ u₃ h) hW
  obtain ⟨h3, h4⟩ := h.not_mu_S3_S4 hW
  rcases l7_10_proved G Ω hP W hW hnc with h1 | h1 | h1
  · exact absurd h1 h3
  · exact absurd h1 h4
  · exact h1

@[expose] def Hyp22SigmaNeX4 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ K₄ ∈ twinSet Ω K, K₄ ≠ K → K₄ ≠ K' → K₄ ≠ K₃ → dComp Ω K ≠ dstarComp Ω K

theorem hyp22SigmaNe_of_split (h3 : Hyp22FourthTwin p f) (h4 : Hyp22SigmaNeX4 p f) :
    Hyp22SigmaNe p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  obtain ⟨K₄, hK₄, h41, h42, h43⟩ := h3 G Ω K K' K₃ z u₁ u₂ u₃ h
  exact h4 G Ω K K' K₃ z u₁ u₂ u₃ h K₄ hK₄ h41 h42 h43

end Wyl

end T7V

end CFSG.ClassicalInvolution.Asc77
