module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalV
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroPrelim
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem centralizer_J₀_inf_centralizer_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) =
      (centralizer (d.J₀ : Set L)).map L.subtype ⊔ zpowers t := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.1 hx
    have hα : ∀ j ∈ d.J₀, h.act ⟨x, hxC⟩ j = j := by
      intro j hj
      apply Subtype.val_injective
      rw [h.coe_act_apply]
      have hc := mem_centralizer_iff.1 hxJ (j : G) ⟨j, hj, rfl⟩
      change x * (j : G) * x⁻¹ = j
      rw [← hc, mul_inv_cancel_right]
    obtain ⟨g, hg, hgα⟩ := d.exists_conj_of_centralizes_J₀ rfl hα
    obtain ⟨c, hc, rfl⟩ := h.exists_mul_zpowers_of_act_eq_conj d hxC hgα
    exact mul_mem (mem_sup_left ⟨g, hg, rfl⟩) (mem_sup_right hc)
  · refine sup_le ?_ ((zpowers_le).2 (Subgroup.mem_inf.2 ⟨?_, h.t_mem_centralizer⟩))
    · rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, h.L_le_centralizer g.2⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 hg j hj)
    · rw [mem_centralizer_iff]
      rintro _ ⟨j, -, rfl⟩
      exact mem_centralizer_iff.1 h.htL _ j.2

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
