module

public import CFSG.GH74.QTGen4.Recog.Ku.A3V2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem E_sup_pCore (h : KuHyp G T M H P z) {E : Subgroup G}
    (hE : E ≤ kuR T M ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧ E ⊓ pCoreOf 2 M = kuV2 T M) :
    E ⊔ pCoreOf 2 M = kuR T M := by
  obtain ⟨hER, -, hEc, hEV⟩ := hE
  have hVR : pCoreOf 2 M ≤ kuR T M := h.pCore_le_kuR
  have hSR : E ⊔ pCoreOf 2 M ≤ kuR T M := sup_le hER hVR
  have hVn : ((pCoreOf 2 M).subgroupOf (kuR T M)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVR]
    intro r hr
    exact h.mem_normalizer_V_of_mem_M (oTwoUpper_le M (show r ∈ kuR T M from hr).2)
  have hVR_card : Nat.card (pCoreOf 2 M) = 16 := h.vCard
  have hrel_R : (pCoreOf 2 M).relIndex (kuR T M) = 4 := by
    have hm := (Subgroup.relIndex_mul_card (H := pCoreOf 2 M) (K := kuR T M))
    rw [inf_eq_left.mpr hVR, h.card_kuR, hVR_card] at hm
    omega
  have hrel_E : (pCoreOf 2 M).relIndex E = 4 := by
    have hm := (Subgroup.relIndex_mul_card (H := pCoreOf 2 M) (K := E))
    rw [inf_comm, hEV, hEc, h.card_kuV2] at hm
    omega
  have hrel_S : (pCoreOf 2 M).relIndex (E ⊔ pCoreOf 2 M) = 4 := by
    rw [← Subgroup.relIndex_subgroupOf (H := pCoreOf 2 M) (K := E ⊔ pCoreOf 2 M) hSR,
      Subgroup.subgroupOf_sup hER hVR, Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf
        (H := pCoreOf 2 M) (K := E) hER, hrel_E]
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 M) (E ⊔ pCoreOf 2 M) (kuR T M)
    le_sup_right hSR
  rw [hrel_S, hrel_R] at hmul
  have h1 : (E ⊔ pCoreOf 2 M).relIndex (kuR T M) = 1 := by omega
  exact le_antisymm hSR (Subgroup.relIndex_eq_one.mp h1)

end KuHyp

end CFSG.GH74.QTGen4.Ku
