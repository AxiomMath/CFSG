module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentInteraction
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentJoins

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BadComponentDetection

theorem le_bad_iff_not_quasisimple {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component) :
    component ≤ TwoComponents.badSubgroup G ↔ ¬ IsQuasisimple component := by
  constructor
  · intro hle
    obtain ⟨containing, hbad, hcontained⟩ := TwoComponentJoins.exists_le_of_le_sSup component
      hcomponent {subgroup : Subgroup G |
        TwoComponents.IsTwoComponent subgroup ∧ ¬ IsQuasisimple subgroup}
      (fun subgroup hmem => hmem.1.1) hle
    have heq := TwoComponentSubnormal.eq_of_le component containing hcomponent hbad.1 hcontained
    exact heq ▸ hbad.2
  · intro hnotQuasisimple
    exact le_sSup ⟨hcomponent, hnotQuasisimple⟩

theorem commutes_with_bad_of_quasisimple {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component)
    (hquasisimple : IsQuasisimple component) :
    ⁅component, TwoComponents.badSubgroup G⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  apply sSup_le
  intro other hbad
  have hne : other ≠ component := fun heq => hbad.2 (heq.symm ▸ hquasisimple)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (TwoComponentInteraction.commutes_of_quasisimple other component hbad.1 hcomponent hne
      (Or.inr hquasisimple))

theorem bad_intersection_le_center {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component)
    (hquasisimple : IsQuasisimple component) :
    (TwoComponents.badSubgroup G).subgroupOf component ≤ Subgroup.center component := by
  have hcentralizer := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutes_with_bad_of_quasisimple component hcomponent hquasisimple)
  intro element hmem
  apply Subgroup.mem_center_iff.mpr
  intro other
  have hcommutes := Subgroup.mem_centralizer_iff.mp (hcentralizer other.property) element.val hmem
  exact Subtype.ext hcommutes.symm

theorem subnormal_monotone {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hsubnormal : IsSubnormal subgroup ⊤) :
    (TwoComponents.badSubgroup subgroup).map subgroup.subtype ≤ TwoComponents.badSubgroup G := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hbad
  apply Subgroup.map_le_iff_le_comap.mp
  apply le_sSup
  refine ⟨TwoComponentTransport.of_subnormal_subgroup subgroup hsubnormal component hbad.1, ?_⟩
  intro hquasisimple
  exact hbad.2 (Components.quasisimple_of_equiv
    (component.equivMapOfInjective subgroup.subtype subgroup.subtype_injective) hquasisimple)

theorem bad_eq_bot_iff {G : Type*} [Group G] [Finite G] :
    TwoComponents.badSubgroup G = ⊥ ↔
      ∀ component : Subgroup G, TwoComponents.IsTwoComponent component → IsQuasisimple component := by
  constructor
  · intro hbot component hcomponent
    exact (TwoComponents.ordinary_of_badSubgroup_eq_bot hbot hcomponent).2.2
  · intro hall
    apply le_antisymm _ bot_le
    apply sSup_le
    intro component hbad
    exact (hbad.2 (hall component hbad.1)).elim

theorem bad_eq_bot_of_subnormal_join {G : Type*} [Group G] [Finite G]
    (subgroups : Set (Subgroup G))
    (hsubnormal : ∀ subgroup ∈ subgroups, IsSubnormal subgroup ⊤)
    (hjoin : sSup subgroups = ⊤)
    (hbad : ∀ subgroup ∈ subgroups, TwoComponents.badSubgroup subgroup = ⊥) :
    TwoComponents.badSubgroup G = ⊥ := by
  apply bad_eq_bot_iff.mpr
  intro component hcomponent
  have hle : component ≤ sSup subgroups := by rw [hjoin]; exact le_top
  obtain ⟨containing, hcontaining, hcontained⟩ := TwoComponentJoins.exists_le_of_le_sSup component
    hcomponent subgroups hsubnormal hle
  have hlocal := TwoComponentTransport.of_overgroup hcomponent hcontained
  have hquasisimple := (bad_eq_bot_iff.mp (hbad containing hcontaining)) _ hlocal
  exact Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hcontained).symm hquasisimple

end CFSG.ComponentClassification.BadComponentDetection
