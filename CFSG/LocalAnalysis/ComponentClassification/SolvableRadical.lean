module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.SolvableRadical

theorem solvable_sup {G : Type*} [Group G] (left right : Subgroup G) [left.Normal]
    [Group.IsSolvable left] [Group.IsSolvable right] : Group.IsSolvable (left ⊔ right : Subgroup G) := by
  let quotient := QuotientGroup.mk' left
  let image := right.map quotient
  let restriction : right →* image :=
    (quotient.domRestrict right).codRestrict image
      (fun member => Subgroup.mem_map_of_mem quotient member.property)
  have hsurjective : Function.Surjective restriction := by
    intro member
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp member.property
    exact ⟨⟨lift, hlift⟩, Subtype.ext heq⟩
  let : Group.IsSolvable image := Group.isSolvable_of_surjective hsurjective
  have himage : (left ⊔ right).map quotient = image := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  let projection : (left ⊔ right : Subgroup G) →* image :=
    (quotient.domRestrict (left ⊔ right)).codRestrict image
      (fun member => himage ▸ Subgroup.mem_map_of_mem quotient member.property)
  let inclusion : left →* (left ⊔ right : Subgroup G) := Subgroup.inclusion le_sup_left
  have hkernel : projection.ker ≤ inclusion.range := by
    intro member hmember
    have hleft : member.val ∈ left := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hmember))
    exact ⟨⟨member.val, hleft⟩, Subtype.ext rfl⟩
  exact Group.isSolvable_of_ker_le_range inclusion projection hkernel

theorem solvable_sSup {G : Type*} [Group G] (subgroups : Set (Subgroup G))
    (hfinite : subgroups.Finite) (hnormal : ∀ subgroup ∈ subgroups, subgroup.Normal)
    (hsolvable : ∀ subgroup ∈ subgroups, Group.IsSolvable subgroup) :
    Group.IsSolvable (sSup subgroups : Subgroup G) := by
  classical
  induction subgroups, hfinite using Set.Finite.induction_on with
  | empty =>
      rw [sSup_empty]
      infer_instance
  | @insert subgroup subgroups hfinite hnotMem hinduction =>
      let : subgroup.Normal := hnormal subgroup (Set.mem_insert _ _)
      let : Group.IsSolvable subgroup := hsolvable subgroup (Set.mem_insert _ _)
      let : Group.IsSolvable (sSup subgroups : Subgroup G) := hinduction
        (fun candidate hcandidate => hnormal candidate (Set.mem_insert_of_mem _ hcandidate))
        (fun candidate hcandidate => hsolvable candidate (Set.mem_insert_of_mem _ hcandidate))
      rw [sSup_insert]
      exact solvable_sup subgroup (sSup subgroups)

@[expose] noncomputable def subgroup (G : Type*) [Group G] : Subgroup G :=
  sSup {candidate : Subgroup G | candidate.Normal ∧ Group.IsSolvable candidate}

theorem normal (G : Type*) [Group G] : (subgroup G).Normal :=
  Subgroup.sSup_normal _ (fun _ hcandidate => hcandidate.1)

theorem solvable (G : Type*) [Group G] [Finite G] : Group.IsSolvable (subgroup G) :=
  solvable_sSup {candidate : Subgroup G | candidate.Normal ∧ Group.IsSolvable candidate}
    (Set.toFinite _) (fun _ hcandidate => hcandidate.1)
    (fun _ hcandidate => hcandidate.2)

theorem maximal {G : Type*} [Group G] (candidate : Subgroup G) [candidate.Normal]
    [Group.IsSolvable candidate] : candidate ≤ subgroup G :=
  le_sSup ⟨inferInstance, inferInstance⟩

theorem characteristic (G : Type*) [Group G] : (subgroup G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro automorphism
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro candidate hcandidate
  let : candidate.Normal := hcandidate.1
  let : Group.IsSolvable candidate := hcandidate.2
  let : (candidate.map automorphism.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance automorphism.toMonoidHom automorphism.surjective
  let : Group.IsSolvable (candidate.map automorphism.toMonoidHom) :=
    Group.isSolvable_of_surjective
      (f := (automorphism.subgroupMap candidate).toMonoidHom)
      (automorphism.subgroupMap candidate).surjective
  exact Subgroup.map_le_iff_le_comap.mp (maximal (candidate.map automorphism.toMonoidHom))

@[expose] def Free (G : Type*) [Group G] : Prop :=
  ∀ candidate : Subgroup G, candidate.Normal → Group.IsSolvable candidate → candidate = ⊥

theorem free_iff_eq_bot (G : Type*) [Group G] [Finite G] : Free G ↔ subgroup G = ⊥ := by
  constructor
  · intro hfree
    exact hfree (subgroup G) (normal G) (solvable G)
  · intro hbot candidate hnormal hsolvable
    let : candidate.Normal := hnormal
    let : Group.IsSolvable candidate := hsolvable
    exact le_bot_iff.mp (hbot ▸ maximal candidate)

theorem free_normal_subgroup {G : Type*} [Group G] [Finite G] (hfree : Free G)
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] : Free normalSubgroup := by
  let radical := subgroup normalSubgroup
  let : radical.Characteristic := characteristic normalSubgroup
  let : Group.IsSolvable radical := solvable normalSubgroup
  let image := radical.map normalSubgroup.subtype
  let : image.Normal := ConjAct.normal_of_characteristic_of_normal
  let restriction : radical →* image :=
    normalSubgroup.subtype.domRestrict radical |>.codRestrict image
      (fun member => Subgroup.mem_map_of_mem normalSubgroup.subtype member.property)
  have hsurjective : Function.Surjective restriction := by
    intro member
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp member.property
    exact ⟨⟨lift, hlift⟩, Subtype.ext heq⟩
  let : Group.IsSolvable image := Group.isSolvable_of_surjective hsurjective
  have himage : image = ⊥ := hfree image inferInstance inferInstance
  apply (free_iff_eq_bot normalSubgroup).mpr
  apply Subgroup.map_subtype_inj.mp
  simpa only [Subgroup.map_bot] using himage

theorem quotient_free (G : Type*) [Group G] [Finite G] :
    letI : (subgroup G).Normal := normal G
    Free (G ⧸ subgroup G) := by
  let : (subgroup G).Normal := normal G
  let : Group.IsSolvable (subgroup G) := solvable G
  let projection := QuotientGroup.mk' (subgroup G)
  intro candidate hnormal hsolvable
  let : candidate.Normal := hnormal
  let : Group.IsSolvable candidate := hsolvable
  let preimage := candidate.comap projection
  let restriction : preimage →* candidate :=
    (projection.domRestrict preimage).codRestrict candidate (fun member => member.property)
  let inclusion : subgroup G →* preimage :=
    Subgroup.inclusion (QuotientGroup.le_comap_mk' (subgroup G) candidate)
  have hkernel : restriction.ker ≤ inclusion.range := by
    intro member hmember
    have hmem : member.val ∈ subgroup G := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hmember))
    exact ⟨⟨member.val, hmem⟩, Subtype.ext rfl⟩
  let : Group.IsSolvable preimage := Group.isSolvable_of_ker_le_range inclusion restriction hkernel
  have hle : preimage ≤ subgroup G := maximal preimage
  have himage := Subgroup.map_mono (f := projection) hle
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self] at himage
  exact le_bot_iff.mp himage

end CFSG.ComponentClassification.SolvableRadical
