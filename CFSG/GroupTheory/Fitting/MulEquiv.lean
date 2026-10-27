module

public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.WholeGroup

variable {A B : Type*} [Group A] [Group B]

theorem fittingSubgroup_map_mulEquiv_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup ⟨hN.1.map e.toMonoidHom e.surjective,
    (Group.isNilpotent_congr (N.equivMapOfInjective e.toMonoidHom e.injective)).mp hN.2⟩

theorem fittingSubgroup_map_mulEquiv (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  refine le_antisymm (fittingSubgroup_map_mulEquiv_le e) fun x hx => ?_
  exact ⟨e.symm x, fittingSubgroup_map_mulEquiv_le e.symm ⟨x, hx, rfl⟩, by simp⟩

theorem generalizedFitting_map_mulEquiv (e : A ≃* B) :
    (generalizedFitting A).map e.toMonoidHom = generalizedFitting B := by
  rw [generalizedFitting, generalizedFitting, Subgroup.map_sup, fittingSubgroup_map_mulEquiv,
    layer_map_mulEquiv]

theorem fittingSubgroup_map_le_of_surjective {C R : Type*} [Group C] [Group R] [Finite C]
    (ψ : C →* R) (hψ : Function.Surjective ψ) : (fittingSubgroup C).map ψ ≤ fittingSubgroup R := by
  have hn : ((fittingSubgroup C).map ψ).Normal := (fittingSubgroup_normal).map ψ hψ
  have hnil : Group.IsNilpotent ↥((fittingSubgroup C).map ψ) :=
    Group.nilpotent_of_surjective (ψ.subgroupMap (fittingSubgroup C))
      (ψ.subgroupMap_surjective _)
  exact le_sSup ⟨hn, hnil⟩

end CFSG.WholeGroup
