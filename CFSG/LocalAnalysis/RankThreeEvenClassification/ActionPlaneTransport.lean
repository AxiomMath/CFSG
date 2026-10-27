module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionPlaneGeneration

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

theorem actionSubgroupFixed_map_le {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (homomorphism : acted →* target)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element)
    (subgroup : Subgroup actor) :
    (actionSubgroupFixed subgroup).map homomorphism ≤ actionSubgroupFixed subgroup := by
  rintro element ⟨preimage, hpreimage, rfl⟩
  apply (mem_actionSubgroupFixed_iff subgroup _).mpr
  intro member
  rw [← hequivariant]
  exact congrArg homomorphism ((mem_actionSubgroupFixed_iff subgroup preimage).mp hpreimage member)

theorem actionPlaneFixedGenerated_map_le {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (prime : ℕ) (homomorphism : acted →* target)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element) :
    (actionPlaneFixedGenerated (actor := actor) (acted := acted) prime).map homomorphism ≤
      actionPlaneFixedGenerated (actor := actor) (acted := target) prime := by
  simp only [actionPlaneFixedGenerated, Subgroup.map_iSup]
  apply iSup_le
  intro plane
  apply iSup_le
  intro hcard
  exact (actionSubgroupFixed_map_le homomorphism hequivariant plane).trans
    (le_iSup_of_le plane (le_iSup_of_le hcard le_rfl))

theorem actionSubgroupFixed_map_eq_of_pGroup_prime_complement_kernel
    {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target] [Finite acted]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (homomorphism : acted →* target) (hsurjective : Function.Surjective homomorphism)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker) (subgroup : Subgroup actor) :
    (actionSubgroupFixed subgroup).map homomorphism = actionSubgroupFixed subgroup := by
  apply le_antisymm (actionSubgroupFixed_map_le homomorphism hequivariant subgroup)
  intro element helement
  obtain ⟨preimage, hpreimageFixed, hpreimage⟩ :=
    exists_fixed_preimage_of_equivariant_pGroup_prime_complement_kernel prime hprime
      (hpgroup.to_subgroup subgroup) homomorphism hsurjective
      (fun member element => hequivariant member element) hkernelComplement element
      ((mem_actionSubgroupFixed_iff subgroup element).mp helement)
  exact ⟨preimage, (mem_actionSubgroupFixed_iff subgroup preimage).mpr hpreimageFixed, hpreimage⟩

theorem actionPlaneFixedGenerated_map_eq_of_pGroup_prime_complement_kernel
    {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target] [Finite acted]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (homomorphism : acted →* target) (hsurjective : Function.Surjective homomorphism)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker) :
    (actionPlaneFixedGenerated (actor := actor) (acted := acted) prime).map homomorphism =
      actionPlaneFixedGenerated (actor := actor) (acted := target) prime := by
  simp only [actionPlaneFixedGenerated, Subgroup.map_iSup,
    actionSubgroupFixed_map_eq_of_pGroup_prime_complement_kernel prime hprime hpgroup
      homomorphism hsurjective hequivariant hkernelComplement]

theorem subgroup_eq_top_of_contains_sylows {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G)
    (hcontains : ∀ prime : ℕ, prime.Prime → ∃ sylow : Sylow prime G, (sylow : Subgroup G) ≤ subgroup) :
    subgroup = ⊤ := by
  apply Subgroup.index_eq_one.mp
  by_contra hne
  obtain ⟨prime, hprime, hdiv⟩ := Nat.exists_prime_and_dvd hne
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨sylow, hle⟩ := hcontains prime hprime
  exact sylow.not_dvd_index (hdiv.trans (Subgroup.index_dvd_of_le hle))

theorem coprime_action_plane_fixed_generated_eq_top {actor : Type u} {acted : Type v}
    [Group actor] [IsMulCommutative actor] [Finite actor]
    [Group acted] [Finite acted] [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (hcomplement : ¬prime ∣ Nat.card acted) :
    actionPlaneFixedGenerated (actor := actor) (acted := acted) prime = ⊤ := by
  apply subgroup_eq_top_of_contains_sylows
  intro sylowPrime hsylowPrime
  have : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  obtain ⟨sylow, hsylow⟩ := exists_invariant_sylow_of_pGroup_action_prime_complement
    prime hprime (IsPGroup.of_card hcard) hcomplement sylowPrime hsylowPrime
    (actor := actor) (acted := acted)
  let subgroup : Subgroup acted := sylow
  have hinvariant : ∀ member : actor, ∀ element ∈ subgroup, member • element ∈ subgroup := by
    intro member element helement
    have hmem := Subgroup.mem_map_of_mem (MulDistribMulAction.toMonoidHom acted member) helement
    rw [hsylow member] at hmem
    exact hmem
  let : MulDistribMulAction actor subgroup := invariantSubgroupAction subgroup hinvariant
  have : Group.IsNilpotent subgroup := sylow.isPGroup'.isNilpotent
  have hsubgroupComplement : ¬prime ∣ Nat.card subgroup :=
    fun hdiv => hcomplement (hdiv.trans (Subgroup.card_subgroup_dvd_card subgroup))
  have htop := solvable_action_plane_fixed_generated_eq_top prime hprime hpower hcard hsubgroupComplement
    (actor := actor) (acted := subgroup)
  have hmap := actionPlaneFixedGenerated_map_le prime subgroup.subtype (fun _ _ => rfl)
    (actor := actor)
  rw [htop] at hmap
  refine ⟨sylow, ?_⟩
  intro element helement
  exact hmap ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩

end CFSG.RankThreeEvenClassification.Helpers
