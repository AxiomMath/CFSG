module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.InvariantsSF
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalV
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem mem_sup_zpowers_of_trivial_S_mod_F (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {c : G} (hcC : c ∈ centralizer ({t} : Set G))
    (hcS : c ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G))
    (hcF : ∀ s ∈ d.S.map L.subtype, c * s * c⁻¹ * s⁻¹ ∈ d.F.map L.subtype) :
    c ∈ d.S.map L.subtype ⊔ zpowers t := by
  have hS : ∀ y ∈ d.S, h.act ⟨c, hcC⟩ y ∈ d.S := by
    intro y hy
    rw [← h.conj_mem_map_iff hcC]
    exact (mem_normalizer_iff.1 hcS (y : G)).1 ⟨y, hy, rfl⟩
  have hα : ∀ y ∈ d.S, h.act ⟨c, hcC⟩ y * y⁻¹ ∈ d.F := by
    intro y hy
    rw [← coe_mem_map_subtype_iff_D4, Subgroup.coe_mul, h.coe_act_apply, Subgroup.coe_inv]
    exact hcF (y : G) ⟨y, hy, rfl⟩
  obtain ⟨n, hn, hact⟩ := d.eq_conj_of_trivial_S_mod_F (α := h.act ⟨c, hcC⟩) hS hα
  obtain ⟨τ, hτ, rfl⟩ := h.exists_mul_zpowers_of_act_eq_conj d hcC hact
  exact mul_mem (mem_sup_left ⟨n, hn, rfl⟩) (mem_sup_right hτ)

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
