module

public import CFSG.Assembly.Defs

public section

open scoped Pointwise

namespace CFSG.ComponentClassification.TwoSubgroupSylowConjugacy

theorem into {G : Type*} [Group G] [Finite G] (ambient twoSubgroup : Subgroup G)
    (htwo : IsPGroup 2 twoSubgroup) (hle : twoSubgroup ≤ ambient) (sylow : Sylow 2 ambient) :
    ∃ actor ∈ ambient, twoSubgroup.map (MulAut.conj actor).toMonoidHom ≤
      (sylow : Subgroup ambient).map ambient.subtype := by
  obtain ⟨containing, hcontained⟩ := (htwo.comap_subtype (K := ambient)).exists_le_sylow
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq ambient containing sylow
  have hmap : ((twoSubgroup.subgroupOf ambient).map (MulAut.conj actor).toMonoidHom) ≤
      (sylow : Subgroup ambient) := by
    have hleMap := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom) hcontained
    have hsubgroupEq := congrArg (fun chosen : Sylow 2 ambient => (chosen : Subgroup ambient)) hactor
    change (containing : Subgroup ambient).map (MulAut.conj actor).toMonoidHom = sylow at hsubgroupEq
    rw [hsubgroupEq] at hleMap
    exact hleMap
  have hambientMap := Subgroup.map_mono (f := ambient.subtype) hmap
  rw [Subgroup.map_map] at hambientMap
  have hcommute : ambient.subtype.comp (MulAut.conj actor).toMonoidHom =
      (MulAut.conj actor.val).toMonoidHom.comp ambient.subtype := by
    ext member
    rfl
  rw [hcommute, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hle] at hambientMap
  exact ⟨actor.val, actor.property, hambientMap⟩

end CFSG.ComponentClassification.TwoSubgroupSylowConjugacy
