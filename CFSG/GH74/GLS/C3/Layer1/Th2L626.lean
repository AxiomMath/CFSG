module

public import CFSG.GH74.GLS.C3.Layer1.Th2L627N

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2.L625

@[expose] def B_lemma626_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsV2StarTriple x y K → HasL2Model (kBar K) (fun q => q = 5) → pRank 2 ↥(CxK x K) = 2 →
      ∀ (t u : G) (J : Subgroup G), IsEStarUnbalMax t u J →
        HasL2Model (kBar J) (fun q => Odd q ∧ IsFM9 q) → pRank 2 ↥(CxK t J) = 2 →
        (∀ c ∈ centralizer ({t} : Set G), ∀ k ∈ J, c * k * c⁻¹ ∈ J) → IsTwoTerminal t J

theorem b_lemma626_of_core
    (h625c1 : B_lemma625c1) (hcore : B_lemma626_core) : B_lemma626 := by
  intro G _ _ hG x y K hV hK5 hCx t u J hmax
  have hlu : IsLocallyUnbalancing t u J := hmax.1.1.isLocallyUnbalancing
  have hrk : pRank 2 ↥(centralizer ({t, u} : Set G)) = 4 :=
    hmax.1.pRank_centralizer hG.pRank_eq_four
  have hL2J := h625c1 G hG x y K hV hK5 hCx t u J hlu hrk
  have hc2 : pRank 2 ↥(CxK t J) = 2 := b_lemma625c2_proved G hG x y K hV hK5 hCx t u J hlu hrk hL2J
  have hL2odd : HasL2Model (kBar J) Odd := by
    obtain ⟨p, f, hp, hf, ⟨hodd, -⟩, hL⟩ := hL2J
    exact ⟨p, f, hp, hf, hodd, hL⟩
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), ∀ k ∈ J, c * k * c⁻¹ ∈ J :=
    normal_of_pRank_le_four hG.pRank_eq_four.le hlu.1 hL2odd
  exact hcore G hG x y K hV hK5 hCx t u J hmax hL2J hc2 hnorm

end CFSG.GH74.GLS
