module

public import CFSG.GH74.QTGen4.Recog.Ku.HGlueC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuA_le_oTwoUpper [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : kuA P H ≤ oTwoUpper M :=
  (h.kuA_le_kuR).trans inf_le_right

theorem kuA_ne_pCore [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA]
    [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : kuA P H ≠ pCoreOf 2 M := by
  intro heq
  have e1 := h.kuA_inf_pCore_M
  rw [heq, inf_idem] at e1
  have e2 : Nat.card (pCoreOf 2 M) = Nat.card (kuV2 T M) := by rw [e1]
  have e3 := h.card_kuV2
  have e4 := h.vCard
  omega

end KuHyp

end CFSG.GH74.QTGen4.Ku
