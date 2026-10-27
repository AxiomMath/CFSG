module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG

theorem mem_elemThompsonFamily_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (p : ℕ) {A : Subgroup X} (hA : A ∈ elemThompsonFamily X p) :
    A.map e.toMonoidHom ∈ elemThompsonFamily Y p :=
  ⟨CFSG.IsElementaryAbelian.subgroup_map hA.1 e.toMonoidHom, by
    rw [Subgroup.card_map_of_injective e.injective, hA.2, CFSG.pRank_congr_of_mulEquiv e p]⟩

theorem elemThompson_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    (elemThompson X p).map e.toMonoidHom = elemThompson Y p := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (mem_elemThompsonFamily_map_mulEquiv e p hA)
  · refine sSup_le fun B hB => ?_
    have hB' : B.map e.symm.toMonoidHom ∈ elemThompsonFamily X p :=
      mem_elemThompsonFamily_map_mulEquiv e.symm p hB
    intro y hy
    have : e.symm y ∈ elemThompson X p := le_sSup hB' ⟨y, hy, rfl⟩
    exact ⟨e.symm y, this, e.apply_symm_apply y⟩

end CFSG
