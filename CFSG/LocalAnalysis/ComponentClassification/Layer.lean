module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.GroupTheory.Fitting.WholeGroupConstruction
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.Layer

@[expose] noncomputable def subgroup (G : Type*) [Group G] : Subgroup G :=
  CFSG.WholeGroup.layerOf fun component : Subgroup G => IsComponentOf component ⊤

theorem subgroup.eq_sSup (G : Type*) [Group G] :
    subgroup G = sSup {component : Subgroup G | IsComponentOf component ⊤} :=
  rfl

attribute [eqns subgroup.eq_sSup] subgroup

theorem component_le {G : Type*} [Group G] {component : Subgroup G}
    (hcomponent : IsComponentOf component ⊤) : component ≤ subgroup G :=
  le_sSup hcomponent

theorem le_derived (G : Type*) [Group G] : subgroup G ≤ commutator G := by
  apply sSup_le
  intro component hcomponent
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  calc
    component = ⁅component, component⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ = commutator G := rfl

theorem normal_component {G : Type*} [Group G] [Finite G] {component : Subgroup G}
    (hcomponent : IsComponentOf component ⊤) :
    (component.subgroupOf (subgroup G)).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  apply sSup_le
  intro other hother
  by_cases heq : other = component
  · rw [heq]
    exact Subgroup.le_normalizer
  · have hcommutes := LocalComponents.commute_of_ne other component hother hcomponent heq
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes).trans
      (Subgroup.centralizer_le_normalizer _)

theorem commutes_with_solvable_subnormal {G : Type*} [Group G] [Finite G]
    (solvableSubgroup : Subgroup G) (hsubnormal : IsSubnormal solvableSubgroup ⊤)
    [Group.IsSolvable solvableSubgroup] : ⁅subgroup G, solvableSubgroup⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  apply sSup_le
  intro component hcomponent
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (LocalComponents.commutes_with_solvable_subnormal component solvableSubgroup
      hcomponent hsubnormal)

theorem map_le_of_equiv {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (subgroup G).map equivalence.toMonoidHom ≤ subgroup H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hcomponent
  exact Subgroup.map_le_iff_le_comap.mp
    (component_le ((LocalComponents.equiv_iff equivalence component).mpr hcomponent))

theorem equiv_invariant {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (subgroup G).map equivalence.toMonoidHom = subgroup H := by
  apply le_antisymm (map_le_of_equiv equivalence)
  intro element hmem
  have hinverse := map_le_of_equiv equivalence.symm
    (Subgroup.mem_map_of_mem equivalence.symm.toMonoidHom hmem)
  exact ⟨equivalence.symm element, hinverse, equivalence.apply_symm_apply element⟩

theorem characteristic (G : Type*) [Group G] : (subgroup G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro automorphism
  exact equiv_invariant automorphism

theorem normal (G : Type*) [Group G] : (subgroup G).Normal := by
  let : (subgroup G).Characteristic := characteristic G
  infer_instance

theorem perfect (G : Type*) [Group G] : Group.IsPerfect (subgroup G) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _) _
  apply sSup_le
  intro component hcomponent
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  rw [← Subgroup.commutator_eq_self (H := component)]
  exact Subgroup.commutator_mono (component_le hcomponent) (component_le hcomponent)

theorem layer_top (G : Type*) [Group G] : subgroup (subgroup G) = ⊤ := by
  have hbound : subgroup G ≤ (subgroup (subgroup G)).map (subgroup G).subtype := by
    apply sSup_le
    intro component hcomponent
    have hle := component_le hcomponent
    rw [← Subgroup.map_subgroupOf_eq_of_le hle]
    exact Subgroup.map_mono (component_le (LocalComponents.of_overgroup hcomponent hle))
  apply top_unique
  intro member _
  obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp (hbound member.property)
  have hidentical : lift = member := Subtype.ext heq
  rwa [hidentical] at hlift

end CFSG.ComponentClassification.Layer
