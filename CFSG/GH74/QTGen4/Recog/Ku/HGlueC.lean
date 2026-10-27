module

public import CFSG.GH74.QTGen4.Recog.Ku.HGlueB
public import CFSG.GH74.QTGen4.Recog.Ku.RStructL
public import CFSG.GH74.QTGen4.Recog.Ku.RStructK

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuA_inf_pCore_M [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA]
    [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : kuA P H ⊓ pCoreOf 2 M = kuV2 T M := by
  refine le_antisymm ?_ ?_
  · intro a ha
    have hP : a ∈ pCoreOf 2 M ⊓ P := by
      rw [← h.pCore_M_inf_pCore_H]
      exact ⟨ha.2, ha.1.1⟩
    have hkW : a ∈ kuA P H ⊓ P := ⟨ha.1, hP.2⟩
    rw [h.kuA_inf_P] at hkW
    rw [← h.kuW_inf_pCore_M]
    exact ⟨hkW, ha.2⟩
  · intro v hv
    exact ⟨h.kuW_le_kuA (h.kuV2_le_kuW hv), hv.1⟩

theorem isElemAbelian_kuA [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : IsElemAbelian 2 (kuA P H) := by
  have hW : ∃ w ∈ kuW P H, w ∉ kuV2 T M := by
    by_contra hc
    have hle : kuW P H ≤ kuV2 T M := fun w hw =>
      Classical.byContradiction fun hn => hc ⟨w, hw, hn⟩
    have hcard := Subgroup.card_le_of_le hle
    have hcW := h.card_kuW
    have hcV2 := h.card_kuV2
    omega
  obtain ⟨w, hw, hwV⟩ := hW
  have hwA : w ∈ kuA P H := h.kuW_le_kuA hw
  have hsq : w * w = 1 := by
    have hel : IsElemAbelian 2 (kuW P H) := h.isElemAbelian_kuW
    have := hel.2 w hw
    rw [← pow_two]
    exact this
  exact h.abelian_complement_elem h.kuA_le_kuR h.isMulCommutative_kuA h.card_kuA
    h.kuA_inf_pCore_M ⟨w, hwA, hwV, hsq⟩

theorem M_inf_normalizer_V2_le_normalizer_kuA [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ≤ Subgroup.normalizer (kuA P H : Set G) :=
  h.M_inf_normalizer_V2_le_normalizer_E (E := kuA P H)
    ⟨h.kuA_le_kuR, h.isElemAbelian_kuA, h.card_kuA, h.kuA_inf_pCore_M⟩

end KuHyp

end CFSG.GH74.QTGen4.Ku
