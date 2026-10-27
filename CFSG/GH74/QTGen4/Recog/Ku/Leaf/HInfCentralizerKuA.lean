module

public import CFSG.GH74.QTGen4.Recog.Ku.LeafWrappers
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.TInfCentralizerKuWLeKuA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem leafHInfCentralizerKuA
    [KuLeaf LeafIsMulCommutativeKuA]
    : LeafHInfCentralizerKuA := by
  intro G _ _ T M H P z h
  apply le_antisymm
  · rintro g ⟨hgH, hgC⟩
    have hgW : g ∈ Subgroup.centralizer (kuW P H : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.kuW_le_kuA) hgC
    exact ⟨h.H_inf_centralizer_kuW_le_pCore ⟨hgH, hgW⟩, hgW⟩
  · intro a ha
    refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H ha.1, ?_⟩
    show a ∈ Subgroup.centralizer (kuA P H : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (h.isMulCommutative_kuA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)

end CFSG.GH74.QTGen4.Ku
