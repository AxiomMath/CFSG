module

public import CFSG.GH74.Generic.S3.Lem36
public import CFSG.GH74.Generic.S3.Lem37

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

namespace Nbhd3

variable {G : Type} [Group G] [Finite G] {t t' : StatedLieTag} {p f : ℕ} {x y : G}
  {Iw Iv Ivw T : Subgroup G} (h : Nbhd3 G t t' p f x y Iw Iv Ivw T)

include h

theorem conf2A (hclass : B_L3_class) (hsyl : B_L3_sylow) (hKT3 : B_L3_noNormalMinus) :
    Conf2A G t p f y x Iv Iw Ivw T := by
  have ht : t' = t := h.tag_eq hKT3 hclass hsyl
  obtain ⟨hcyc, hnL, hnU, -⟩ := h.lem34 hclass hsyl
  refine
    { tag := h.tag
      prime := h.prime
      v_inv := h.y_inv
      w_inv := h.x_inv
      comm := h.comm
      ne := h.ne
      comp_v := h.comp_v
      comp_w := h.comp_w
      comp_vw := h.comp_vw
      v_mem := h.y_Iv
      iso_v := h.Iv_iso
      model_w := h.model_w
      model_vw := by rw [← ht]; exact h.model_vw
      odd_w := h.odd_w
      odd_vw := h.odd_vw
      le_w := h.Iv_le
      le_vw := h.Iv_le_vw
      notConj_w := h.not_isConj_y_x hclass hsyl
      notConj_vw := h.not_isConj_y_yx hclass hsyl
      sylow_w := h.T_sylow
      sylow_vw := h.T_sylow_vw hclass hsyl
      v_P := h.y_R.1
      w_P := h.x_T
      v_central := h.y_comm_T
      Q_iso := h.lem37_Q_iso hclass hsyl
      Q_cyc := hcyc
      Q_exp := ⟨fun hh => ?_, fun hh => ?_⟩ }
  · exact Monoid.exponent_dvd.2 fun a => by
      rw [← Subgroup.orderOf_coe a]
      exact hnL (ht.trans hh) a a.2
  · exact Monoid.exponent_dvd.2 fun a => by
      rw [← Subgroup.orderOf_coe a]
      exact hnU (ht.trans hh) a a.2

end Nbhd3

end CFSG.GH74.Generic.S3
