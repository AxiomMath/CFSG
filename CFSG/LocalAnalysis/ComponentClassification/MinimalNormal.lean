module

public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalNormal

@[expose] def Property {G : Type*} [Group G] (subgroup : Subgroup G) : Prop :=
  Minimal (fun candidate : Subgroup G => candidate.Normal ∧ candidate ≠ ⊥) subgroup

theorem exists_le {G : Type*} [Group G] [Finite G]
    (overgroup : Subgroup G) [overgroup.Normal] (hne : overgroup ≠ ⊥) :
    ∃ subgroup : Subgroup G, subgroup ≤ overgroup ∧ Property subgroup := by
  let candidates : Set (Subgroup G) :=
    {candidate | candidate.Normal ∧ candidate ≠ ⊥ ∧ candidate ≤ overgroup}
  obtain ⟨subgroup, hminimal⟩ := (Set.toFinite candidates).exists_minimal
    (show candidates.Nonempty from ⟨overgroup, inferInstance, hne, le_rfl⟩)
  refine ⟨subgroup, hminimal.prop.2.2, minimal_iff.mpr ⟨?_, ?_⟩⟩
  · exact ⟨hminimal.prop.1, hminimal.prop.2.1⟩
  · intro smaller hsmaller hle
    exact (minimal_iff.mp hminimal).2 ⟨hsmaller.1, hsmaller.2, hle.trans hminimal.prop.2.2⟩ hle

theorem equiv_image {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (subgroup : Subgroup G) (hminimal : Property subgroup) :
    Property (subgroup.map equivalence.toMonoidHom) := by
  let : subgroup.Normal := hminimal.prop.1
  have himageNormal : (subgroup.map equivalence.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance equivalence.toMonoidHom equivalence.surjective
  have himageNe : subgroup.map equivalence.toMonoidHom ≠ ⊥ := by
    intro hbot
    have hle := (Subgroup.map_eq_bot_iff subgroup).mp hbot
    apply hminimal.prop.2
    apply le_antisymm _ bot_le
    intro element hmem
    exact Subgroup.mem_bot.mpr (equivalence.injective
      ((MonoidHom.mem_ker.mp (hle hmem)).trans equivalence.map_one.symm))
  apply minimal_iff.mpr
  refine ⟨⟨himageNormal, himageNe⟩, ?_⟩
  intro smaller hsmaller hle
  let : smaller.Normal := hsmaller.1
  have hpreimageNe : smaller.comap equivalence.toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hsmaller.2
    have heq := Subgroup.map_comap_eq_self_of_surjective
      (f := equivalence.toMonoidHom) equivalence.surjective smaller
    rw [hbot, Subgroup.map_bot] at heq
    exact heq.symm
  have hpreimageLe : smaller.comap equivalence.toMonoidHom ≤ subgroup := by
    have hcomap := Subgroup.comap_mono (f := equivalence.toMonoidHom) hle
    rwa [Subgroup.comap_map_eq_self_of_injective equivalence.injective] at hcomap
  have heq : subgroup = smaller.comap equivalence.toMonoidHom :=
    (minimal_iff.mp hminimal).2 ⟨inferInstance, hpreimageNe⟩ hpreimageLe
  rw [heq, Subgroup.map_comap_eq_self_of_surjective
    (f := equivalence.toMonoidHom) equivalence.surjective]

theorem commutative_of_solvable {G : Type*} [Group G]
    (subgroup : Subgroup G) (hminimal : Property subgroup) [Group.IsSolvable subgroup] :
    IsMulCommutative subgroup := by
  let : subgroup.Normal := hminimal.prop.1
  let ambientDerived := (commutator subgroup).map subgroup.subtype
  let : ambientDerived.Normal := ConjAct.normal_of_characteristic_of_normal
  have hle : ambientDerived ≤ subgroup := Subgroup.map_subtype_le _
  have hbot : ambientDerived = ⊥ := by
    by_contra hne
    have heq : subgroup = ambientDerived :=
      (minimal_iff.mp hminimal).2 ⟨inferInstance, hne⟩ hle
    have hperfect : commutator subgroup = ⊤ := by
      apply Subgroup.map_subtype_inj.mp
      change ambientDerived = (⊤ : Subgroup subgroup).map subgroup.subtype
      have htop : (⊤ : Subgroup subgroup).map subgroup.subtype = subgroup := by
        apply le_antisymm (Subgroup.map_subtype_le _) _
        intro element hmem
        exact Subgroup.mem_map.mpr ⟨⟨element, hmem⟩, Subgroup.mem_top _, rfl⟩
      rw [htop]
      exact heq.symm
    let : Group.IsPerfect subgroup := ⟨hperfect⟩
    let : Nontrivial subgroup := subgroup.nontrivial_iff_ne_bot.mpr hminimal.prop.2
    exact Group.IsPerfect.not_isSolvable subgroup inferInstance
  have hderived : commutator subgroup = ⊥ := by
    apply Subgroup.map_subtype_inj.mp
    simpa only [Subgroup.map_bot] using hbot
  exact (commutator_eq_bot_iff subgroup).mp hderived

theorem elementaryAbelian_of_solvable {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hminimal : Property subgroup) [Group.IsSolvable subgroup] :
    ∃ prime : ℕ, prime.Prime ∧ IsElemAbelian prime subgroup ∧ IsPGroup prime subgroup := by
  classical
  let : subgroup.Normal := hminimal.prop.1
  let : IsMulCommutative subgroup := commutative_of_solvable subgroup hminimal
  let : Nontrivial subgroup := subgroup.nontrivial_iff_ne_bot.mpr hminimal.prop.2
  obtain ⟨prime, hprime, hdivides⟩ := Nat.exists_prime_and_dvd
    (show Nat.card subgroup ≠ 1 from fun hone => hminimal.prop.2 (Subgroup.card_eq_one.mp hone))
  let : Fact prime.Prime := ⟨hprime⟩
  let power : subgroup →* subgroup :=
    { toFun := fun element => element ^ prime
      map_one' := one_pow prime
      map_mul' := fun left right =>
        (show Commute left right from (isMulCommutative_iff.mp inferInstance) left right).mul_pow prime }
  let torsion := power.ker
  let : torsion.Characteristic := ⟨by
    intro automorphism
    ext element
    change (automorphism element) ^ prime = 1 ↔ element ^ prime = 1
    rw [← map_pow]
    exact ⟨fun heq => automorphism.injective (heq.trans automorphism.map_one.symm),
      fun heq => by rw [heq, map_one]⟩⟩
  let ambientTorsion := torsion.map subgroup.subtype
  let : ambientTorsion.Normal := ConjAct.normal_of_characteristic_of_normal
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' prime hdivides
  have helementMem : element ∈ torsion := orderOf_dvd_iff_pow_eq_one.mp (horder ▸ dvd_rfl)
  have helementNe : element ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at horder
    exact hprime.ne_one horder.symm
  have hne : ambientTorsion ≠ ⊥ := by
    intro hbot
    have hmem := Subgroup.mem_map_of_mem subgroup.subtype helementMem
    change element.val ∈ ambientTorsion at hmem
    rw [hbot] at hmem
    exact helementNe (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have heq : subgroup = ambientTorsion :=
    (minimal_iff.mp hminimal).2 ⟨inferInstance, hne⟩ (Subgroup.map_subtype_le _)
  have hpower : ∀ element : subgroup, element ^ prime = 1 := by
    intro element
    have hmem : element.val ∈ ambientTorsion := heq ▸ element.property
    obtain ⟨lift, hlift, hvalue⟩ := Subgroup.mem_map.mp hmem
    have helements : lift = element := Subtype.ext hvalue
    exact helements ▸ hlift
  refine ⟨prime, hprime, ⟨inferInstance, ?_⟩, ?_⟩
  · intro element hmem
    exact congrArg Subtype.val (hpower ⟨element, hmem⟩)
  · exact isPGroup_iff_pow_pow_eq_one.mpr fun element => ⟨1, by simpa using hpower element⟩

end CFSG.ComponentClassification.MinimalNormal
