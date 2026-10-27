module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42GData
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SetupG
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4Y
public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Model2
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Transport

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem e₂_mem_centralizer : d.e₂ ∈ centralizer ({d.e₂} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem t_mem_centralizer_e₂ (h : d.Hyp) : d.t ∈ centralizer ({d.e₂} : Set G) :=
  mem_centralizer_singleton_iff.2 h.e₂_comm_t.symm

theorem e₂_not_mem_center (h : d.Hyp) : d.e₂ ∉ center G := by
  haveI := h.simple
  have hz : center G = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonab).2
  rw [hz, mem_bot]
  exact d.e₂_ne_one

theorem U_le_centralizer_e₂ : d.U ≤ centralizer ({d.e₂} : Set G) := inf_le_right

theorem zpowers_t_inf_e₂K₃ (h : d.Hyp) : zpowers d.t ⊓ (zpowers d.e₂ ⊔ d.K₃) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxt, hxM⟩ := mem_inf.1 hx
  rcases CFSG.LocalAnalysis.SteinbergBK.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two h.t_two
      hxt with h1 | h1
  · rw [h1]
    exact one_mem _
  · exfalso
    rw [h1] at hxM
    exact h.t_not_mem_e₂_sup_K₃ hxM

theorem gomiU42SetupG (h : d.Hyp) (hYsq : ∀ y ∈ d.Y, y * y = 1) :
    GomiU42SetupG G (centralizer ({d.e₂} : Set G)) d.e₂ d.t d.K₃ d.E₂ := by
  have hU := h.sec4_6_U
  have hE := h.sec4_6_E₂
  refine
    { e_mem := e₂_mem_centralizer
      t_mem := h.t_mem_centralizer_e₂
      kGroup := CFSG.ComponentClassification.TBLit.isKGroupCat_centralizer
        h.setting.setting.kProper h.e₂_not_mem_center
      e_central := fun y hy => mem_centralizer_singleton_iff.1 hy
      orderOf_e := d.orderOf_e₂
      t_sq := h.t_mul_t
      t_ne_one := h.t_ne_one
      J₀_le := d.K₃_le_centralizer_e₂
      lieModel := ?_
      le_centralizer := fun x hx =>
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h.t_mem x (d.pull_le_L _ hx))
      inf_e := d.zpowers_e₂_inf_K₃
      centralizer_eq := h.centralizer_e₂_inf_H
      inf_t := h.zpowers_t_inf_e₂K₃
      two_pow_dvd := ?_
      E₂_le := ?_
      elementary := ?_
      card_E₂ := h.card_E₂
      mem_normalizer := hE.2.2.2.2.2.2.2.2 (h.t_mem_U)
      isPGroup_sup := ?_
      card_inf := ?_
      inf_le := ?_ }
  · have e : ↥d.K₃ ≃* ↥StabSub :=
      (MulEquiv.subgroupCongr d.K₃_eq_pull_StabSub).trans
        (Subgroup.equivMapOfInjective StabSub d.ι d.ι_injective).symm
    exact lieModel_of_mulEquiv_classical e (by decide) lieModel_StabSub
  · have := Subgroup.card_dvd_of_le (U_le_centralizer_e₂ (d := d))
    rw [hU.2.2.2.1] at this
    exact this
  · exact hE.2.1.trans U_le_centralizer_e₂
  · have hY := h.Y_eq_E₂
    refine CFSG.IsElementaryAbelian.two_of_forall_mul_self ?_ ?_
    · intro a ha b hb
      have ha' : a ∈ d.Y := hY ▸ ha
      have hb' : b ∈ d.Y := hY ▸ hb
      have hbD : b ∈ d.D₀ := (mem_inf.1 hb').2
      exact (mem_centralizer_iff.1 (mem_inf.1 ha').1 b hbD).symm
    · intro a ha
      exact hYsq a (hY ▸ ha)
  · rw [hE.2.2.2.1]
    exact IsPGroup.of_card hU.2.2.2.1
  · rw [show d.E₂ ⊓ centralizer ({d.t} : Set G) = d.F from hE.2.2.2.2.1, d.card_F]
  · rw [show d.E₂ ⊓ centralizer ({d.t} : Set G) = d.F from hE.2.2.2.2.1]
    exact d.F_le_K₃

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
