module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.Open.OrderForm

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OddCore

theorem odd_card_sup {G : Type*} [Group G] (left right : Subgroup G) [left.Normal]
    (hleft : Odd (Nat.card left)) (hright : Odd (Nat.card right)) :
    Odd (Nat.card (left ⊔ right : Subgroup G)) := by
  have hindex : Odd (left.relIndex right) :=
    hright.of_dvd_nat (left.relIndex_dvd_card right)
  have hcard : Nat.card left * left.relIndex (left ⊔ right) =
      Nat.card (left ⊔ right : Subgroup G) := by
    have hmul := (left.subgroupOf (left ⊔ right)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at hmul
    exact hmul
  rw [Subgroup.relIndex_sup_left right left] at hcard
  rw [← hcard]
  exact hleft.mul hindex

theorem odd_card_sSup {G : Type*} [Group G] (subgroups : Set (Subgroup G))
    (hfinite : subgroups.Finite)
    (hnormal : ∀ subgroup ∈ subgroups, subgroup.Normal)
    (hodd : ∀ subgroup ∈ subgroups, Odd (Nat.card subgroup)) :
    Odd (Nat.card (sSup subgroups : Subgroup G)) := by
  induction subgroups, hfinite using Set.Finite.induction_on with
  | empty => simp
  | @insert subgroup subgroups hnotmem hfinite hinduction =>
      rw [sSup_insert]
      let : subgroup.Normal := hnormal subgroup (by simp)
      apply odd_card_sup
      · exact hodd subgroup (by simp)
      · apply hinduction
        · intro member hmember
          exact hnormal member (by simp [hmember])
        · intro member hmember
          exact hodd member (by simp [hmember])

theorem odd_card (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (componentClassificationOddCore G)) := by
  apply odd_card_sSup _ (Set.toFinite _)
  · exact fun _ hmember => hmember.1
  · exact fun _ hmember => hmember.2

theorem maximal (G : Type*) [Group G] (subgroup : Subgroup G)
    (hnormal : subgroup.Normal) (hodd : Odd (Nat.card subgroup)) :
    subgroup ≤ componentClassificationOddCore G := by
  exact le_sSup ⟨hnormal, hodd⟩

theorem char_invariant {G : Type*} [Group G] (automorphism : G ≃* G) :
    (componentClassificationOddCore G).map automorphism.toMonoidHom =
      componentClassificationOddCore G := by
  have hmap : ∀ equivalence : G ≃* G,
      (componentClassificationOddCore G).map equivalence.toMonoidHom ≤
        componentClassificationOddCore G := by
    intro equivalence
    apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro source hsource
    apply Subgroup.map_le_iff_le_comap.mp
    apply maximal
    · exact hsource.1.map equivalence.toMonoidHom equivalence.surjective
    · rw [← Nat.card_congr
        (source.equivMapOfInjective equivalence.toMonoidHom equivalence.injective).toEquiv]
      exact hsource.2
  apply le_antisymm (hmap automorphism)
  intro element hmem
  have hinverse : automorphism.symm element ∈ componentClassificationOddCore G :=
    hmap automorphism.symm (Subgroup.mem_map_of_mem automorphism.symm.toMonoidHom hmem)
  exact Subgroup.mem_map.mpr ⟨automorphism.symm element, hinverse,
    automorphism.apply_symm_apply element⟩

theorem quotient_corefree (G : Type*) [Group G] [Finite G] :
    componentClassificationOddCore (G ⧸ componentClassificationOddCore G) = ⊥ := by
  let core := componentClassificationOddCore G
  let quotient := QuotientGroup.mk' core
  let quotientCore := componentClassificationOddCore (G ⧸ core)
  let preimage : Subgroup G := quotientCore.comap quotient
  have hkernel : quotient.ker = core := QuotientGroup.ker_mk' core
  have hle : core ≤ preimage := by
    rw [← hkernel]
    exact Subgroup.ker_le_comap quotient quotientCore
  have hmap : preimage.map quotient = quotientCore :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective core) quotientCore
  have hcard : Nat.card core * core.relIndex preimage = Nat.card preimage := by
    have hmul := (core.subgroupOf preimage).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hmul
    exact hmul
  have hindex : core.relIndex preimage = Nat.card quotientCore := by
    have hrel := Subgroup.relIndex_ker preimage quotient
    rw [hkernel, hmap] at hrel
    exact hrel
  have hodd : Odd (Nat.card preimage) := by
    rw [← hcard, hindex]
    exact (odd_card G).mul (odd_card (G ⧸ core))
  have hpreimage : preimage ≤ core :=
    maximal G preimage (Subgroup.Normal.comap inferInstance quotient) hodd
  apply le_antisymm _ bot_le
  change quotientCore ≤ ⊥
  rw [← hmap]
  intro element hmem
  obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmem
  apply Subgroup.mem_bot.mpr
  apply MonoidHom.mem_ker.mp
  rw [hkernel]
  exact hpreimage hlift

theorem characteristic (G : Type*) [Group G] :
    (componentClassificationOddCore G).Characteristic := by
  exact Subgroup.characteristic_iff_map_eq.mpr char_invariant

theorem normal_intersection (G : Type*) [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] :
    (componentClassificationOddCore normalSubgroup).map normalSubgroup.subtype =
      normalSubgroup ⊓ componentClassificationOddCore G := by
  let : (componentClassificationOddCore normalSubgroup).Characteristic :=
    characteristic normalSubgroup
  have hcore : (componentClassificationOddCore normalSubgroup).map normalSubgroup.subtype ≤
      componentClassificationOddCore G := by
    apply maximal
    · infer_instance
    · rw [Subgroup.card_subtype]
      exact odd_card normalSubgroup
  apply le_antisymm (le_inf (Subgroup.map_subtype_le _) hcore)
  rw [inf_comm, ← Subgroup.subgroupOf_map_subtype]
  apply Subgroup.map_mono
  apply maximal
  · exact Subgroup.Normal.comap inferInstance normalSubgroup.subtype
  · have hcard : Nat.card ((componentClassificationOddCore G).subgroupOf normalSubgroup) =
        Nat.card (componentClassificationOddCore G ⊓ normalSubgroup : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
    rw [hcard]
    exact (odd_card G).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem map_le_of_equiv {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (componentClassificationOddCore G).map equivalence.toMonoidHom ≤
      componentClassificationOddCore H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro source hsource
  apply Subgroup.map_le_iff_le_comap.mp
  apply maximal
  · exact hsource.1.map equivalence.toMonoidHom equivalence.surjective
  · rw [← Nat.card_congr
      (source.equivMapOfInjective equivalence.toMonoidHom equivalence.injective).toEquiv]
    exact hsource.2

theorem equiv_invariant {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (componentClassificationOddCore G).map equivalence.toMonoidHom =
      componentClassificationOddCore H := by
  apply le_antisymm (map_le_of_equiv equivalence)
  intro element hmem
  have hinverse : equivalence.symm element ∈ componentClassificationOddCore G :=
    map_le_of_equiv equivalence.symm
      (Subgroup.mem_map_of_mem equivalence.symm.toMonoidHom hmem)
  exact Subgroup.mem_map.mpr ⟨equivalence.symm element, hinverse,
    equivalence.apply_symm_apply element⟩

theorem normal_step_mem_iff {G : Type*} [Group G] [Finite G]
    {lower upper : Subgroup G} (hle : lower ≤ upper) [(lower.subgroupOf upper).Normal]
    (element : lower) :
    element ∈ componentClassificationOddCore lower ↔
      Subgroup.inclusion hle element ∈ componentClassificationOddCore upper := by
  let equivalence := Subgroup.subgroupOfEquivOfLe hle
  have hintersection := normal_intersection upper (lower.subgroupOf upper)
  have hmem : ∀ member : lower.subgroupOf upper,
      member ∈ componentClassificationOddCore (lower.subgroupOf upper) ↔
        member.val ∈ componentClassificationOddCore upper := by
    intro member
    rw [← Subgroup.mem_map_iff_mem (lower.subgroupOf upper).subtype_injective,
      hintersection]
    change member.val ∈ lower.subgroupOf upper ∧ _ ↔ _
    exact and_iff_right member.property
  rw [← equiv_invariant equivalence, Subgroup.mem_map_equiv]
  exact hmem (equivalence.symm element)

theorem subnormal_mem_iff {G : Type*} [Group G] [Finite G]
    {lower upper : Subgroup G} (hsubnormal : IsSubnormal lower upper)
    (element : G) (hmem : element ∈ lower) :
    (⟨element, hmem⟩ : lower) ∈ componentClassificationOddCore lower ↔
      ∃ hupper : element ∈ upper,
        (⟨element, hupper⟩ : upper) ∈ componentClassificationOddCore upper := by
  induction hsubnormal with
  | refl subgroup =>
      exact ⟨fun hcore => ⟨hmem, hcore⟩, fun ⟨_, hcore⟩ => hcore⟩
  | @step lower middle upper hle hnormal hsubnormal hinduction =>
      let : (lower.subgroupOf middle).Normal := hnormal
      rw [normal_step_mem_iff hle]
      exact hinduction (hle hmem)

theorem subnormal_corefree {G : Type*} [Group G] [Finite G]
    (hcorefree : componentClassificationOddCore G = ⊥) (subgroup : Subgroup G)
    (hsubnormal : IsSubnormal subgroup ⊤) : componentClassificationOddCore subgroup = ⊥ := by
  apply le_antisymm _ bot_le
  intro element hmem
  obtain ⟨htop, hcore⟩ := (subnormal_mem_iff hsubnormal element.val element.property).mp hmem
  have hintersection := normal_intersection G (⊤ : Subgroup G)
  have hmap := Subgroup.mem_map_of_mem (⊤ : Subgroup G).subtype hcore
  rw [hintersection, hcorefree, inf_bot_eq] at hmap
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hmap))

theorem subnormal_intersection {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hsubnormal : IsSubnormal subgroup ⊤) :
    componentClassificationOddCore subgroup =
      (componentClassificationOddCore G).subgroupOf subgroup := by
  ext element
  change element ∈ componentClassificationOddCore subgroup ↔
    element.val ∈ componentClassificationOddCore G
  have htop : ∀ member : (⊤ : Subgroup G),
      member ∈ componentClassificationOddCore (⊤ : Subgroup G) ↔
        member.val ∈ componentClassificationOddCore G := by
    intro member
    rw [← Subgroup.mem_map_iff_mem (⊤ : Subgroup G).subtype_injective,
      normal_intersection G (⊤ : Subgroup G)]
    exact and_iff_right member.property
  constructor
  · intro hcore
    obtain ⟨hmem, hmember⟩ :=
      (subnormal_mem_iff hsubnormal element.val element.property).mp hcore
    exact (htop ⟨element.val, hmem⟩).mp hmember
  · intro hcore
    apply (subnormal_mem_iff hsubnormal element.val element.property).mpr
    exact ⟨Subgroup.mem_top element.val,
      (htop ⟨element.val, Subgroup.mem_top element.val⟩).mpr hcore⟩

end CFSG.ComponentClassification.OddCore
