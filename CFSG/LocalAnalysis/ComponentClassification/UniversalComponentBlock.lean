module

public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentTransport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.UniversalComponentBlock

@[expose] def Universal {G : Type*} [Group G] (component : Subgroup G) : Prop :=
  ∀ involution : G, orderOf involution = 2 →
    involution ∈ Subgroup.centralizer (component : Set G) →
    IsComponentOf (component.subgroupOf (Subgroup.centralizer {involution})) ⊤

@[expose] def Related {G : Type*} [Group G] (first second : Subgroup G) : Prop :=
  first = second ∨ ⁅first, second⁆ = ⊥

theorem related_refl {G : Type*} [Group G] (component : Subgroup G) :
    Related component component := Or.inl rfl

theorem related_symm {G : Type*} [Group G] {first second : Subgroup G}
    (hrelated : Related first second) : Related second first := by
  rcases hrelated with heq | hcommutes
  · exact Or.inl heq.symm
  · exact Or.inr (by rwa [Subgroup.commutator_comm])

theorem component_le_involution_centralizer {G : Type*} [Group G]
    (component : Subgroup G) (involution : G)
    (hcentralizes : involution ∈ Subgroup.centralizer (component : Set G)) :
    component ≤ Subgroup.centralizer {involution} := by
  intro member hmember
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hcentralizes member hmember)

theorem commuting_neighbor_component {G : Type*} [Group G] [Finite G]
    (component neighbor : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : Universal neighbor) (hcommutes : ⁅neighbor, component⁆ = ⊥) :
    IsComponentOf (neighbor.subgroupOf (Subgroup.centralizer (component : Set G))) ⊤ := by
  have hdivides : 2 ∣ Nat.card component := by
    obtain ⟨half, hhalf⟩ := heven
    exact ⟨half, by omega⟩
  obtain ⟨involution, horder⟩ := exists_prime_orderOf_dvd_card' (G := component) 2 hdivides
  have hambientOrder : orderOf involution.val = 2 := by
    exact (orderOf_injective component.subtype component.subtype_injective involution).trans horder
  have hcentralizes : involution.val ∈ Subgroup.centralizer (neighbor : Set G) := by
    have hreverse : ⁅component, neighbor⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hreverse involution.property
  have hneighbor := huniversal involution.val hambientOrder hcentralizes
  have hneighborLe := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes
  have hcentralizerLe : Subgroup.centralizer (component : Set G) ≤
      Subgroup.centralizer {involution.val} := by
    intro member hmember
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hmember involution.val involution.property).symm
  exact OrdinaryComponentTransport.restrict_nested neighbor _ _ hneighborLe hcentralizerLe hneighbor

theorem related_trans {G : Type*} [Group G] [Finite G]
    (first middle last : Subgroup G) (heven : Even (Nat.card middle))
    (hfirst : Universal first) (hlast : Universal last)
    (hfirstMiddle : Related first middle) (hmiddleLast : Related middle last) :
    Related first last := by
  rcases hfirstMiddle with heq | hfirstCommutes
  · subst first
    exact hmiddleLast
  rcases hmiddleLast with heq | hlastCommutes
  · subst last
    exact Or.inr hfirstCommutes
  by_cases heq : first = last
  · exact Or.inl heq
  · right
    have hlastReverse : ⁅last, middle⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
    exact OrdinaryComponentTransport.commute_local_distinct first last _
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hfirstCommutes)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hlastReverse)
      (commuting_neighbor_component middle first heven hfirst hfirstCommutes)
      (commuting_neighbor_component middle last heven hlast hlastReverse) heq

theorem singleton_centralizer_map {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (member : G) :
    (Subgroup.centralizer {member}).map equivalence.toMonoidHom =
      Subgroup.centralizer {equivalence member} := by
  ext other
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro heq
    simpa only [map_mul, equivalence.apply_symm_apply] using congrArg equivalence heq
  · intro heq
    simpa only [map_mul, equivalence.symm_apply_apply] using congrArg equivalence.symm heq

theorem centralizing_image {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (component : Subgroup G) (member : G)
    (hcentralizes : member ∈ Subgroup.centralizer (component : Set G)) :
    equivalence member ∈ Subgroup.centralizer (component.map equivalence.toMonoidHom : Set H) := by
  apply Subgroup.mem_centralizer_iff.mpr
  rintro other ⟨lift, hlift, rfl⟩
  exact (equivalence.toMonoidHom.map_mul lift member).symm.trans
    ((congrArg equivalence (Subgroup.mem_centralizer_iff.mp hcentralizes lift hlift)).trans
      (equivalence.toMonoidHom.map_mul member lift))

theorem subgroup_centralizer_map {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (component : Subgroup G) :
    (Subgroup.centralizer (component : Set G)).map equivalence.toMonoidHom =
      Subgroup.centralizer (component.map equivalence.toMonoidHom : Set H) := by
  ext member
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    exact centralizing_image equivalence component lift hlift
  · intro hmember
    have hcentralizes : equivalence.symm member ∈ Subgroup.centralizer (component : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro other hother
      apply equivalence.injective
      rw [map_mul, map_mul, equivalence.apply_symm_apply]
      exact Subgroup.mem_centralizer_iff.mp hmember (equivalence other)
        (Subgroup.mem_map_of_mem equivalence.toMonoidHom hother)
    exact ⟨equivalence.symm member, hcentralizes, equivalence.apply_symm_apply member⟩

theorem universal_map {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (component : Subgroup G) (huniversal : Universal component) :
    Universal (component.map equivalence.toMonoidHom) := by
  intro involution horder hcentralizes
  let preimage := equivalence.symm involution
  have hpreimageOrder : orderOf preimage = 2 := by
    exact (orderOf_injective equivalence.symm.toMonoidHom
      equivalence.symm.injective involution).trans horder
  have hpreimageCentralizes : preimage ∈ Subgroup.centralizer (component : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have heq := Subgroup.mem_centralizer_iff.mp hcentralizes (equivalence member)
      (Subgroup.mem_map_of_mem equivalence.toMonoidHom hmember)
    simpa only [map_mul, equivalence.symm_apply_apply] using congrArg equivalence.symm heq
  have hcomponent := OrdinaryComponentTransport.map_nested equivalence component
    (Subgroup.centralizer {preimage}) (huniversal preimage hpreimageOrder hpreimageCentralizes)
  rw [singleton_centralizer_map, show equivalence preimage = involution from
    equivalence.apply_symm_apply involution] at hcomponent
  exact hcomponent

theorem related_map_iff {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (first second : Subgroup G) :
    Related (first.map equivalence.toMonoidHom) (second.map equivalence.toMonoidHom) ↔
      Related first second := by
  constructor
  · rintro (heq | hcommutes)
    · exact Or.inl (Subgroup.map_injective equivalence.injective heq)
    · right
      apply Subgroup.map_injective (f := equivalence.toMonoidHom) equivalence.injective
      simpa only [Subgroup.map_commutator, Subgroup.map_bot] using hcommutes
  · rintro (heq | hcommutes)
    · exact Or.inl (congrArg (Subgroup.map equivalence.toMonoidHom) heq)
    · right
      have hmap := congrArg (Subgroup.map equivalence.toMonoidHom) hcommutes
      simpa only [Subgroup.map_commutator, Subgroup.map_bot] using hmap

end CFSG.ComponentClassification.UniversalComponentBlock
