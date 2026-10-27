module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeAct
public import CFSG.LocalAnalysis.OddStandard.Seitz77V1ActPlane
public import CFSG.LocalAnalysis.OddStandard.Seitz77WLocalDef

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

section Config

variable {G : Type} [Group G] [Finite G] {A W X O : Subgroup G} {t : G}

@[expose] noncomputable def IsSetting25.config25 (S : IsSetting25 A W t X O)
    [(O.subgroupOf X).Normal] (L : Levi.LeviData A W) (F : ActionFacts A W) :
    Config25 (Q25 X O) S.phiW.range S.tbar where
  card_Q := S.card_Q25
  V_central := S.phiW_range_le_center
  card_V := S.card_phiW_range
  elem_V := S.elem_phiW_range
  t_sq := S.tbar_mul_self
  t_not_mem := S.tbar_not_mem
  centralizer_t := S.centralizer_tbar
  comm_mem := S.comm_tbar
  ι := (MonoidHom.ofInjective S.phiW_injective).symm.trans L.ι
  αUp := S.alphaUp L F
  αLow := S.alphaLow L F
  αTor := S.alphaTor L
  αTor_cube := S.alphaTor_cube L F
  fix_t := ⟨fun γ => S.alphaUp_tbar L F (Multiplicative.toAdd γ),
    fun γ => S.alphaLow_tbar L F (Multiplicative.toAdd γ), S.alphaTor_tbar L⟩
  act_up := fun γ v => by
    show S.alphaUp L F (Multiplicative.ofAdd γ) (S.phiW (L.ι.symm (Multiplicative.ofAdd v))) =
      S.phiW (L.ι.symm (Multiplicative.ofAdd (cUp γ v)))
    rw [S.alphaUp_phiW L F]
    have h := (L.act_u γ).conj_eq (L.ι.symm (Multiplicative.ofAdd v))
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact congrArg S.phiW h
  act_low := fun γ v => by
    show S.alphaLow L F (Multiplicative.ofAdd γ) (S.phiW (L.ι.symm (Multiplicative.ofAdd v))) =
      S.phiW (L.ι.symm (Multiplicative.ofAdd (cLow γ v)))
    rw [S.alphaLow_phiW L F]
    have h := (L.act_l γ).conj_eq (L.ι.symm (Multiplicative.ofAdd v))
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact congrArg S.phiW h
  act_tor := fun v => by
    show S.alphaTor L (S.phiW (L.ι.symm (Multiplicative.ofAdd v))) =
      S.phiW (L.ι.symm (Multiplicative.ofAdd (dTor v)))
    rw [S.alphaTor_phiW L]
    have h := L.act_τ.conj_eq (L.ι.symm (Multiplicative.ofAdd v))
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact congrArg S.phiW h

end Config

section OfPlane

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ W : Subgroup G}

theorem IsSetting25.ofPlaneData
    (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) (pl : PlaneData d W) :
    IsSetting25 A W d.t pl.X pl.O := by
  obtain ⟨hWV, hWab, hW16⟩ := hR.property hW
  obtain ⟨-, hEab, hE32⟩ := h.adj_properties d hR hW
  have hmem : ∀ w ∈ W, d.t * w ∈ W ⊔ zpowers d.t := fun w hw =>
    mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hw)
  exact
    { W_le_A := fun w hw => (hWV hw).2
      W_elem := hWab
      W_card := hW16
      t_sq := d.t_mul_self
      t_cent := d.t_mem_K
      t_not_mem := fun hw => h.facts.t_not_mem_V d (hWV hw)
      E_elem := hEab
      E_card := hE32
      norm_le := pl.norm_le
      X_le := pl.reg.le_normalizer
      normalizer_le := pl.reg.normalizer_le
      cent_le := pl.reg.centralizer_le
      index_cent := pl.reg.relIndex_eq
      conj_t := fun x hx => by
        have hx' : x * d.t * x⁻¹ ∈ W ⊔ zpowers d.t :=
          (mem_normalizer_iff.mp hx d.t).mp (mem_sup_right (mem_zpowers _))
        exact (h.isConj_iff_mem_coset d hR hW hx').mp (isConj_iff.mpr ⟨x, rfl⟩)
      trans := fun w hw => pl.reg.exists_conj (d.t * w) (hmem w hw)
        ((h.isConj_iff_mem_coset d hR hW (hmem w hw)).mpr ⟨w, hw, rfl⟩)
      X_cent := pl.X_cent
      O_odd := pl.O_odd
      O_norm := pl.O_norm
      O_sup := pl.O_sup
      odd_inf := h.odd_inf
      cent_t := (centralizer_t_facts d.sector).1 }

theorem Hyp.actionFacts
    (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) : ActionFacts A W :=
  ⟨h.centralizer_radical_le d hR hW, h.card_fixed_le_four d hR hW, h.relIndex_le_four d hR hW⟩

end OfPlane

end CFSG.OddStandard.Seitz77
