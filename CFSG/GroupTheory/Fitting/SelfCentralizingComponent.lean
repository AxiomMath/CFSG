module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG

variable {G : Type*} [Group G]

theorem layer_eq_of_isComponent_of_centralizer_eq_bot [Finite G] (Q : Subgroup G)
    (hQ : IsComponent Q) (hC : Subgroup.centralizer (Q : Set G) = ⊥) : layer G = Q := by
  apply le_antisymm
  · apply sSup_le
    intro K hK
    rcases LocalCores.distinct_components_commute hK hQ with h | h
    · exact h.le
    · have hKbot : K = ⊥ :=
        le_bot_iff.mp (hC ▸ Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
      exact hKbot ▸ bot_le
  · exact le_sSup hQ

theorem fittingSubgroup_eq_bot_of_isComponent_of_centralizer_eq_bot [Finite G] (Q : Subgroup G)
    (hQ : IsComponent Q) (hC : Subgroup.centralizer (Q : Set G) = ⊥) : fittingSubgroup G = ⊥ :=
  le_bot_iff.mp (hC ▸ Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (layer_eq_of_isComponent_of_centralizer_eq_bot Q hQ hC ▸
      LocalCores.fitting_layer_commute (G := G)))

theorem generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot [Finite G] (Q : Subgroup G)
    (hQ : IsComponent Q) (hC : Subgroup.centralizer (Q : Set G) = ⊥) :
    generalizedFitting G = Q := by
  rw [generalizedFitting, fittingSubgroup_eq_bot_of_isComponent_of_centralizer_eq_bot Q hQ hC,
    layer_eq_of_isComponent_of_centralizer_eq_bot Q hQ hC, bot_sup_eq]

end CFSG
