module

public import CFSG.GH74.QTGen4.Recog.Ku.HStruct
public import CFSG.GH74.QTGen4.Recog.Ku.LeafWrappers
public import CFSG.GH74.QTGen4.Recog.Ku.TCent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem not_pCore_M_le_pCore_H [KuLeaf LeafEqKuAOfElemAbelian]
    (h : KuHyp G T M H P z) : ¬ pCoreOf 2 M ≤ pCoreOf 2 H := by
  intro hVQ
  have hV : pCoreOf 2 M = kuA P H := h.eq_kuA_of_elemAbelian hVQ h.vElem h.vCard
  have hHM : H ≤ M := by
    intro g hg
    rw [h.mNorm]
    have hN := h.H_le_normalizer_kuA hg
    rw [← hV] at hN
    exact hN
  have hHT : H ≤ T := by
    rw [h.T_eq_inf]
    exact le_inf hHM le_rfl
  have hle := Subgroup.card_le_of_le hHT
  rw [h.card_H, h.card_T] at hle
  omega

theorem z_mem_kuA (h : KuHyp G T M H P z) : z ∈ kuA P H :=
  kuW_le_kuA h (z_mem_kuW h)

end KuHyp

end CFSG.GH74.QTGen4.Ku
