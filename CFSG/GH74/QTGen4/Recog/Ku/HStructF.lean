module

public import CFSG.GH74.QTGen4.Recog.Ku.Defs
public import CFSG.GH74.QTGen4.Recog.Ku.HStructC
public import CFSG.GH74.QTGen4.Recog.Ku.HStructD

public section

namespace CFSG.GH74.QTGen4.Ku

open scoped commutatorElement

namespace KuHyp

variable {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G}

theorem exists_mem_pCoreOf_not_mem (h : KuHyp G T M H P z) :
    ∃ u ∈ CFSG.Open.pCoreOf 2 H, u ∉ P := by
  by_contra hc
  push Not at hc
  have hle : CFSG.Open.pCoreOf 2 H ≤ P := fun x hx => hc x hx
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_pCore_H_aux, h.pExtra.2.1] at h1
  omega

theorem exists_comm_not_mem_zpowers (h : KuHyp G T M H P z) :
    ∃ u ∈ CFSG.Open.pCoreOf 2 H, ∃ p ∈ P, ⁅p, u⁆ ∉ Subgroup.zpowers z := by
  obtain ⟨u, huQ, huP⟩ := h.exists_mem_pCoreOf_not_mem
  have huH : u ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H huQ
  refine ⟨u, huQ, ?_⟩
  by_contra hc
  push Not at hc
  have hgP : ∀ p ∈ P, u * p * u⁻¹ * p⁻¹ ∈ Subgroup.zpowers z := by
    intro p hp
    have h1 : (⁅p, u⁆ : G)⁻¹ ∈ Subgroup.zpowers z := Subgroup.inv_mem _ (hc p hp)
    have e : (⁅p, u⁆ : G)⁻¹ = u * p * u⁻¹ * p⁻¹ := by
      rw [commutatorElement_def]
      group
    rwa [e] at h1
  exact huP (h.mem_P_of_acts_trivially_aux huH hgP)

theorem exists_mem_kuW_not_mem_zpowers (h : KuHyp G T M H P z) :
    ∃ c ∈ kuW P H, c ∉ Subgroup.zpowers z := by
  obtain ⟨u, huQ, p, hp, hnot⟩ := h.exists_comm_not_mem_zpowers
  exact ⟨⁅p, u⁆, Subgroup.commutator_mem_commutator hp huQ, hnot⟩

end KuHyp

end CFSG.GH74.QTGen4.Ku
