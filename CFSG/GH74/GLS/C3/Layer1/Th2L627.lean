module

public import CFSG.GH74.GLS.C3.Layer1.Th2L627Q
public import CFSG.GH74.GLS.C3.Layer1.Th2L627N

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2.L625 CFSG.GH74.GLS.C3.Layer1

@[expose] def B_lemma627_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsV2StarTriple x y K → HasL2Model (kBar K) (fun q => q = 5) → pRank 2 ↥(CxK x K) = 2 →
      ∀ (t u : G) (J : Subgroup G), IsEStarUnbalMax t u J → IsTwoTerminal t J →
        IsV2Triple t u J → ∀ (t' u' : G) (J' : Subgroup G), IsV2Triple t' u' J' →
          twoPartCard (centralizer ({t'} : Set G)) ≤ twoPartCard (centralizer ({t} : Set G))

namespace Th2.L625

theorem not_u2Succ_of_five
    {H J : Type} [Group H] [Group J] (hH : InU2 H) (hH5 : HasL2Model H (fun q => q = 5))
    (hJ5 : HasL2Model J (fun q => q = 5)) : ¬ U2Succ H J := by
  rintro ⟨-, -, hA | hB | hC⟩
  · obtain ⟨⟨e⟩, -⟩ := hA
    have h60 := card_of_l2_five hH5
    have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [Nat.card_congr e.toEquiv, h7] at h60
    omega
  · obtain ⟨hnC, -⟩ := hB
    obtain ⟨p, f, hp, hf, h5, hL⟩ := hH5
    exact hnC (inC2_of_l2_fm9 hH ⟨p, f, hp, hf, h5 ▸ Th2Tstar.isFM9_five, hL⟩)
  · obtain ⟨-, hlt⟩ := hC
    have h1 := card_of_l2_five hH5
    have h2 := card_of_l2_five hJ5
    omega

theorem v2triple_data
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hfm : ClassFM9)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K : Subgroup G}
    (hV : IsV2StarTriple x y K) (hK5 : HasL2Model (kBar K) (fun q => q = 5))
    {v w : G} {H : Subgroup G} (hv : IsV2Triple v w H) :
    HasL2Model (kBar H) (fun q => q = 5) ∧ pRank 2 ↥(CxK v H) = 2 ∧
      (∀ c ∈ centralizer ({v} : Set G), ∀ k ∈ H, c * k * c⁻¹ ∈ H) ∧
      twoPartCard (centralizer ({v} : Set G)) = 8 * twoPartCard (CxK v H) ∧
      NxK v H = centralizer ({v} : Set G) := by
  have hlu : IsLocallyUnbalancing v w H := hv.1
  have hH5 : HasL2Model (kBar H) (fun q => q = 5) := lemma625a_of h102 hL34 hfm hG hV hK5 hv
  have hL2odd : HasL2Model (kBar H) Odd := by
    obtain ⟨p, f, hp, hf, h5, hL⟩ := hH5
    exact ⟨p, f, hp, hf, by rw [h5]; decide, hL⟩
  have hup : pRank 2 ↥(CxK v H) ≤ 2 := by
    have h1 := pRank_CxK_add_two_le hlu.1 hL2odd
    have h2 := hG.pRank_eq_four
    omega
  have hlow : 2 ≤ pRank 2 ↥(CxK v H) := by
    rcases hv.2.2.1 with h | hexc
    · exact h
    · exact absurd hexc.2.1 (Th2.not_nonempty_A7_of_hasL2Model hH5)
  have hnorm : ∀ c ∈ centralizer ({v} : Set G), ∀ k ∈ H, c * k * c⁻¹ ∈ H :=
    normal_of_pRank_le_four hG.pRank_eq_four.le hlu.1 hL2odd
  refine ⟨hH5, le_antisymm hup hlow, hnorm, twoPartCard_centralizer_eq_eight_mul hlu hH5 hnorm, ?_⟩
  exact inf_eq_left.2 fun c hc => U1a.mem_normalizer_of_norm hnorm hc

end Th2.L625

theorem b_lemma627_of_core
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hfm : ClassFM9) (h625c1 : B_lemma625c1)
    (hcore : B_lemma627_core) : B_lemma627 := by
  intro G _ _ hG x y K hV hK5 hCx t u J hmax hterm
  have hlu : IsLocallyUnbalancing t u J := hmax.1.1.isLocallyUnbalancing
  have hrk : pRank 2 ↥(centralizer ({t, u} : Set G)) = 4 :=
    hmax.1.pRank_centralizer hG.pRank_eq_four
  have hL2J := h625c1 G hG x y K hV hK5 hCx t u J hlu hrk
  have hc2 : pRank 2 ↥(CxK t J) = 2 := b_lemma625c2_proved G hG x y K hV hK5 hCx t u J hlu hrk hL2J
  have hU2J : InU2 (kBar J) := h102 G hG t u J hlu
  have hno : ¬ IsL34Quotient (kBar J) := fun hl34 =>
    hL34 G hG.gen4 t J hlu.1.1 hlu.1.2 ⟨hl34, (inU2_center hU2J).1, (inU2_center hU2J).2⟩
  have hV2 : IsV2Triple t u J := ⟨hlu, hterm, Or.inl hc2.ge, fun hl34 => absurd hl34 hno⟩
  have hdata : ∀ {v w : G} {H : Subgroup G}, IsV2Triple v w H →
      HasL2Model (kBar H) (fun q => q = 5) ∧ pRank 2 ↥(CxK v H) = 2 ∧
        (∀ c ∈ centralizer ({v} : Set G), ∀ k ∈ H, c * k * c⁻¹ ∈ H) ∧
        twoPartCard (centralizer ({v} : Set G)) = 8 * twoPartCard (CxK v H) ∧
        NxK v H = centralizer ({v} : Set G) :=
    fun hv => v2triple_data h102 hL34 hfm hG hV hK5 hv
  have hmax1 : V2Max1 t u J := ⟨hV2, fun x' y' K' h' =>
    not_u2Succ_of_five (h102 G hG x' y' K' h'.1) (hdata h').1 (hdata hV2).1⟩
  have hmax2 : V2Max2 t u J := ⟨hmax1, fun x' y' K' h1 =>
    ((hdata h1.1).2.1.trans hc2.symm).le⟩
  have hmax3 : V2Max3 t u J := ⟨hmax2, fun x' y' K' h2 => by
    have hv' : IsV2Triple x' y' K' := h2.1.1
    have hle := hcore G hG x y K hV hK5 hCx t u J hmax hterm hV2 x' y' K' hv'
    rw [(hdata hv').2.2.2.1, (hdata hV2).2.2.2.1] at hle
    omega⟩
  refine ⟨hmax3, fun x' y' K' h3 => ?_⟩
  have hv' : IsV2Triple x' y' K' := h3.1.1.1
  rw [(hdata hv').2.2.2.2, (hdata hV2).2.2.2.2]
  exact hcore G hG x y K hV hK5 hCx t u J hmax hterm hV2 x' y' K' hv'

end CFSG.GH74.GLS
