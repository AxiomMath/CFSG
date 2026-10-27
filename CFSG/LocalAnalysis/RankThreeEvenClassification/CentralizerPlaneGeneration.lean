module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionPlaneGeneration

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose, instance_reducible]
def normalizedConjugationAction {G : Type u} [Group G]
    (actor subgroup : Subgroup G)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    MulDistribMulAction actor subgroup where
  smul member element := ⟨member * element * (member : G)⁻¹,
    Subgroup.le_normalizer_iff.mp hnormalizes member member.property element element.property⟩
  one_smul element := Subtype.ext (by
    change (1 : G) * (element : G) * (1 : G)⁻¹ = element
    simp)
  mul_smul first second element := Subtype.ext (by
    change ((first : G) * second) * (element : G) * ((first : G) * second)⁻¹ =
      first * ((second : G) * element * (second : G)⁻¹) * (first : G)⁻¹
    simp [mul_assoc])
  smul_one member := Subtype.ext (by
    change (member : G) * 1 * (member : G)⁻¹ = 1
    simp)
  smul_mul member first second := Subtype.ext (by
    change (member : G) * ((first : G) * second) * (member : G)⁻¹ =
      (member * first * (member : G)⁻¹) * (member * second * (member : G)⁻¹)
    simp [mul_assoc])

theorem actionSubgroupFixed_map_conjugation_eq {G : Type u} [Group G]
    (actor subgroup : Subgroup G)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G))
    (plane : Subgroup actor) :
    letI := normalizedConjugationAction actor subgroup hnormalizes
    (actionSubgroupFixed (acted := subgroup) plane).map subgroup.subtype =
      subgroup ⊓ Subgroup.centralizer (plane.map actor.subtype : Set G) := by
  let : MulDistribMulAction actor subgroup := normalizedConjugationAction actor subgroup hnormalizes
  ext element
  constructor
  · rintro ⟨preimage, hpreimage, rfl⟩
    refine ⟨preimage.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro member ⟨internal, hinternal, rfl⟩
    have hfixed := (mem_actionSubgroupFixed_iff plane preimage).mp hpreimage ⟨internal, hinternal⟩
    have hconjugate := congrArg (fun value : subgroup => (value : G)) hfixed
    change (internal : G) * (preimage : G) * (internal : G)⁻¹ = (preimage : G) at hconjugate
    have hmul := congrArg (fun value : G => value * internal) hconjugate
    change (internal : G) * (preimage : G) = (preimage : G) * internal
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  · rintro ⟨hsubgroup, hcentralizer⟩
    refine ⟨⟨element, hsubgroup⟩, ?_, rfl⟩
    apply (mem_actionSubgroupFixed_iff plane _).mpr
    intro member
    apply Subtype.ext
    change ((member : actor) : G) * element * ((member : actor) : G)⁻¹ = element
    rw [Subgroup.mem_centralizer_iff.mp hcentralizer (member : actor)
      (Subgroup.mem_map_of_mem actor.subtype member.property), mul_inv_cancel_right]

theorem solvable_centralizer_generation_of_rank_three_actor
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup : Subgroup G)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (hsolvable : Group.IsSolvable subgroup)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    subgroup = ⨆ (plane : Subgroup G) (_ : plane ≤ actor) (_ : Nat.card plane = prime ^ 2),
      subgroup ⊓ Subgroup.centralizer (plane : Set G) := by
  have : IsMulCommutative actor := hcomm
  have : Group.IsSolvable subgroup := hsolvable
  let : MulDistribMulAction actor subgroup := normalizedConjugationAction actor subgroup hnormalizes
  have htop := solvable_action_plane_fixed_generated_eq_top prime hprime hpower hcard hcomplement
    (actor := actor) (acted := subgroup)
  have hmapLe : (actionPlaneFixedGenerated (actor := actor) (acted := subgroup) prime).map subgroup.subtype ≤
      ⨆ (plane : Subgroup G) (_ : plane ≤ actor) (_ : Nat.card plane = prime ^ 2),
        subgroup ⊓ Subgroup.centralizer (plane : Set G) := by
    simp only [actionPlaneFixedGenerated, Subgroup.map_iSup]
    apply iSup_le
    intro plane
    apply iSup_le
    intro hplaneCard
    rw [actionSubgroupFixed_map_conjugation_eq actor subgroup hnormalizes plane]
    have hcardMap : Nat.card (plane.map actor.subtype) = prime ^ 2 :=
      (card_map_eq_of_injOn actor.subtype plane actor.subtype_injective.injOn).trans hplaneCard
    exact le_iSup_of_le (plane.map actor.subtype)
      (le_iSup_of_le (Subgroup.map_subtype_le plane) (le_iSup_of_le hcardMap le_rfl))
  rw [htop] at hmapLe
  apply le_antisymm
  · intro element helement
    exact hmapLe ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩
  · apply iSup_le
    intro plane
    apply iSup_le
    intro _
    apply iSup_le
    intro _
    exact inf_le_left

theorem exists_plane_fixed_not_le_of_rank_three_actor
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup lower : Subgroup G)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (hsolvable : Group.IsSolvable subgroup)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G)) (hnotLe : ¬subgroup ≤ lower) :
    ∃ plane : Subgroup G, plane ≤ actor ∧ Nat.card plane = prime ^ 2 ∧
      ¬subgroup ⊓ Subgroup.centralizer (plane : Set G) ≤ lower := by
  classical
  by_contra hexists
  apply hnotLe
  rw [solvable_centralizer_generation_of_rank_three_actor prime hprime actor subgroup hcomm hpower
    hcard hsolvable hcomplement hnormalizes]
  apply iSup_le
  intro plane
  apply iSup_le
  intro hle
  apply iSup_le
  intro hplaneCard
  by_contra hnotLe
  exact hexists ⟨plane, hle, hplaneCard, hnotLe⟩

end CFSG.RankThreeEvenClassification.Helpers
