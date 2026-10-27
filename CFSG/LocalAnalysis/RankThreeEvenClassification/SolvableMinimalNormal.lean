module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryCore
public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def MinimalNontrivialNormal {G : Type u} [Group G] (subgroup : Subgroup G) : Prop :=
  Minimal (fun candidate : Subgroup G => candidate.Normal ∧ candidate ≠ ⊥) subgroup

theorem exists_minimal_nontrivial_normal {G : Type u} [Group G] [Finite G] [Nontrivial G] :
    ∃ subgroup : Subgroup G, MinimalNontrivialNormal subgroup := by
  have htopNe : (⊤ : Subgroup G) ≠ ⊥ := top_ne_bot
  obtain ⟨subgroup, _, hminimal⟩ := Finite.exists_le_minimal
    (p := fun candidate : Subgroup G => candidate.Normal ∧ candidate ≠ ⊥)
      (a := ⊤) ⟨inferInstance, htopNe⟩
  exact ⟨subgroup, hminimal⟩

theorem minimal_normal_solvable_commutative {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G) (hminimal : MinimalNontrivialNormal subgroup)
    (hsolvable : Group.IsSolvable subgroup) : IsMulCommutative subgroup := by
  have : subgroup.Normal := hminimal.1.1
  have : Group.IsSolvable subgroup := hsolvable
  have : Nontrivial subgroup := (Subgroup.nontrivial_iff_ne_bot subgroup).mpr hminimal.1.2
  have hcharacteristic : (commutator subgroup).Characteristic := by
    rw [commutator_def]
    infer_instance
  have : (commutator subgroup).Characteristic := hcharacteristic
  let derived := (commutator subgroup).map subgroup.subtype
  have hderivedNormal : derived.Normal := ConjAct.normal_of_characteristic_of_normal
  have hderivedBot : derived = ⊥ := by
    by_contra hne
    have heq := hminimal.eq_of_le ⟨hderivedNormal, hne⟩ (Subgroup.map_subtype_le _)
    have htop : commutator subgroup = ⊤ := by
      apply Subgroup.map_injective subgroup.subtype_injective
      change derived = (⊤ : Subgroup subgroup).map subgroup.subtype
      rw [heq]
      ext element
      exact ⟨fun hmem => ⟨⟨element, hmem⟩, Subgroup.mem_top _, rfl⟩,
        fun ⟨preimage, _, heq⟩ => heq ▸ preimage.property⟩
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial subgroup).ne htop
  apply (commutator_eq_bot_iff subgroup).mp
  exact (Subgroup.map_eq_bot_iff_of_injective (commutator subgroup) subgroup.subtype_injective).mp hderivedBot

theorem minimal_normal_solvable_elementary {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G) (hminimal : MinimalNontrivialNormal subgroup)
    (hsolvable : Group.IsSolvable subgroup) :
    ∃ prime : ℕ, prime.Prime ∧ IsElemAbelian prime subgroup ∧
      ∃ dimension : ℕ, 0 < dimension ∧ Nat.card subgroup = prime ^ dimension := by
  classical
  have : subgroup.Normal := hminimal.1.1
  have hcomm := minimal_normal_solvable_commutative subgroup hminimal hsolvable
  have : IsMulCommutative subgroup := hcomm
  let : CommGroup subgroup := IsMulCommutative.instCommGroup
  have hcardNe : Nat.card subgroup ≠ 1 := fun heq => hminimal.1.2 (Subgroup.card_eq_one.mp heq)
  obtain ⟨prime, hprime, hdiv⟩ := Nat.exists_prime_and_dvd hcardNe
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨element, helementOrder⟩ := exists_prime_orderOf_dvd_card' prime hdiv
  let killed := (powMonoidHom (α := subgroup) prime).ker
  have hkilledCharacteristic : killed.Characteristic := by
    apply Subgroup.characteristic_iff_map_le.mpr
    intro automorphism
    rintro member ⟨preimage, hpreimage, rfl⟩
    change automorphism preimage ^ prime = 1
    rw [← map_pow]
    change preimage ^ prime = 1 at hpreimage
    rw [hpreimage, map_one]
  have : killed.Characteristic := hkilledCharacteristic
  let ambientKilled := killed.map subgroup.subtype
  have hambientNormal : ambientKilled.Normal := ConjAct.normal_of_characteristic_of_normal
  have helementNe : element ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at helementOrder
    exact hprime.ne_one helementOrder.symm
  have hambientNe : ambientKilled ≠ ⊥ := by
    intro heq
    have hpower : element ^ prime = 1 := helementOrder ▸ pow_orderOf_eq_one element
    have hmem : (element : G) ∈ ambientKilled := Subgroup.mem_map_of_mem subgroup.subtype hpower
    rw [heq, Subgroup.mem_bot] at hmem
    exact helementNe (Subtype.ext hmem)
  have heq := hminimal.eq_of_le ⟨hambientNormal, hambientNe⟩ (Subgroup.map_subtype_le killed)
  have hpower : ∀ member ∈ subgroup, member ^ prime = 1 := by
    intro member hmember
    have hmem : member ∈ ambientKilled := heq.symm ▸ hmember
    obtain ⟨preimage, hpreimage, hpreimageEq⟩ := hmem
    have hpowerInternal : preimage ^ prime = 1 := hpreimage
    have hambientPower := congrArg (fun value : subgroup => (value : G)) hpowerInternal
    have hvalue : (preimage : G) = member := hpreimageEq
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hvalue] using hambientPower
  have hab : IsElemAbelian prime subgroup := ⟨hcomm, hpower⟩
  obtain ⟨dimension, hdimension⟩ := (isElemAbelian_isPGroup prime subgroup hab).exists_card_eq
  have hdimensionPos : 0 < dimension := by
    by_contra hnot
    have hzero : dimension = 0 := by omega
    rw [hzero, pow_zero] at hdimension
    exact hcardNe hdimension
  exact ⟨prime, hprime, hab, dimension, hdimensionPos, hdimension⟩

end CFSG.RankThreeEvenClassification.Helpers
