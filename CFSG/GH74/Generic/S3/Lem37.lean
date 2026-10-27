module

public import CFSG.GH74.Generic.S3.Lem34

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

namespace Nbhd3

variable {G : Type} [Group G] [Finite G] {t t' : StatedLieTag} {p f : ℕ} {x y : G}
  {Iw Iv Ivw T : Subgroup G} (h : Nbhd3 G t t' p f x y Iw Iv Ivw T)

include h

theorem T_conj_Rxy : ∀ s ∈ T, ∀ r ∈ T ⊓ Ivw, s * r * s⁻¹ ∈ T ⊓ Ivw := fun s hs r hr =>
  ⟨T.mul_mem (T.mul_mem hs hr.1) (T.inv_mem hs), h.T_conj_Ivw s hs r hr.2⟩

theorem Rxy_inf_C_Iw : (T ⊓ Ivw) ⊓ centralizer (Iw : Set G) = ⊥ := by
  apply inf_eq_bot_of_no_involution
    (h.T_pGroup.to_le (show (T ⊓ Ivw) ⊓ centralizer (Iw : Set G) ≤ T from fun a ha => ha.1.1))
  intro a ha hb haa
  by_contra ha1
  rcases h.Q_involution a ⟨ha.1, hb⟩ haa with h1 | h1
  · exact ha1 h1
  · exact h.x_notin_Ivw (h1 ▸ ha.2)

theorem R_inf_C_Ivw : (T ⊓ Iw) ⊓ centralizer (Ivw : Set G) = ⊥ := by
  apply inf_eq_bot_of_no_involution
    (h.T_pGroup.to_le (show (T ⊓ Iw) ⊓ centralizer (Ivw : Set G) ≤ T from fun a ha => ha.1.1))
  intro a ha hb haa
  by_contra ha1
  rcases h.Qxy_involution a ⟨ha.1, hb⟩ haa with h1 | h1
  · exact ha1 h1
  · exact h.yx_notin_Iw (h1 ▸ ha.2)

theorem tag_eq (hKT3 : B_L3_noNormalMinus) (hclass : B_L3_class) (hsyl : B_L3_sylow) : t' = t := by
  by_contra hne
  have hq := h.comp_w.1.isQuasisimple
  have hq' := h.comp_vw.1.isQuasisimple
  rcases h.tag with ht | ht <;> rcases h.tag' with ht' | ht'
  · exact hne (ht'.trans ht.symm)
  ·
    exact hKT3 G t t' p f ⟨ht, ht'⟩ h.prime.1 h.prime.2.1 h.prime.2.2 Iw hq h.odd_w
      h.model_w (centralizer ({x} : Set G)) T h.Iw_le h.centralizer_le_normalizer h.T_sylow (T ⊓ Ivw)
      inf_le_left (normal_of_normIn inf_le_left h.T_conj_Rxy) h.Rxy_inf_C_Iw G Ivw (T ⊓ Ivw) hq'
      h.odd_vw h.model_vw (h.Rxy_sylow hclass hsyl) ⟨MulEquiv.refl _⟩
  ·
    exact hKT3 G t' t p f ⟨ht', ht⟩ h.prime.1 h.prime.2.1 h.prime.2.2 Ivw hq' h.odd_vw
      h.model_vw (centralizer ({y * x} : Set G)) T h.comp_vw.1.1 h.comp_vw.le_normalizer
      (h.T_sylow_vw hclass hsyl) (T ⊓ Iw) inf_le_left
      (normal_of_normIn inf_le_left h.T_conj_R) h.R_inf_C_Ivw G Iw (T ⊓ Iw) hq h.odd_w h.model_w
      h.R_sylow ⟨MulEquiv.refl _⟩
  · exact hne (ht'.trans ht.symm)

end Nbhd3

end CFSG.GH74.Generic.S3
