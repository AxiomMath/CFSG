module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableActionGeneration

public section

open scoped commutatorElement

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem solvable_centralizer_generation_of_plane {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup : Subgroup G)
    (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 2) (hsolvable : Group.IsSolvable subgroup)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    subgroup = ⨆ (member : actor) (_ : member ≠ 1),
      subgroup ⊓ Subgroup.centralizer {(member : G)} := by
  have : Group.IsSolvable subgroup := hsolvable
  let action : MulDistribMulAction actor subgroup :=
    { smul := fun member element => ⟨member * element * (member : G)⁻¹,
        Subgroup.le_normalizer_iff.mp hnormalizes member member.property element element.property⟩
      one_smul := fun element => Subtype.ext (by
        change (1 : G) * (element : G) * (1 : G)⁻¹ = element
        simp)
      mul_smul := fun first second element => Subtype.ext (by
        change ((first : G) * second) * (element : G) * ((first : G) * second)⁻¹ =
          first * ((second : G) * element * (second : G)⁻¹) * (first : G)⁻¹
        simp [mul_assoc])
      smul_one := fun member => Subtype.ext (by
        change (member : G) * 1 * (member : G)⁻¹ = 1
        simp)
      smul_mul := fun member first second => Subtype.ext (by
        change (member : G) * ((first : G) * second) * (member : G)⁻¹ =
          (member * first * (member : G)⁻¹) * (member * second * (member : G)⁻¹)
        simp [mul_assoc]) }
  let : MulDistribMulAction actor subgroup := action
  have hfixedMap : ∀ member : actor,
      (actionFixedSubgroup member).map subgroup.subtype =
        subgroup ⊓ Subgroup.centralizer {(member : G)} := by
    intro member
    ext element
    constructor
    · rintro ⟨preimage, hpreimage, rfl⟩
      refine ⟨preimage.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hconjugate := congrArg (fun value : subgroup => (value : G)) hpreimage
      change (member : G) * (preimage : G) * (member : G)⁻¹ = (preimage : G) at hconjugate
      have hmul := congrArg (fun value : G => value * member) hconjugate
      have hcommute : (member : G) * (preimage : G) = preimage * member := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
      exact hcommute.symm
    · rintro ⟨hsubgroup, hcentralizer⟩
      refine ⟨⟨element, hsubgroup⟩, ?_, rfl⟩
      apply Subtype.ext
      change (member : G) * element * (member : G)⁻¹ = element
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hcentralizer, mul_inv_cancel_right]
  have htop := solvable_action_fixed_generated_eq_top prime hprime hpower hcard hcomplement
    (actor := actor) (acted := subgroup)
  have hmap := congrArg (fun part : Subgroup subgroup => part.map subgroup.subtype) htop
  simp only [actionFixedGenerated, Subgroup.map_iSup, hfixedMap] at hmap
  have htopMap : (⊤ : Subgroup subgroup).map subgroup.subtype = subgroup := by
    ext element
    exact ⟨fun ⟨preimage, _, heq⟩ => heq ▸ preimage.property,
      fun helement => ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩⟩
  exact (hmap.trans htopMap).symm

@[expose] noncomputable def repeatedActionCommutators {G : Type u} [Group G]
    (actor subgroup : Subgroup G) : Subgroup G :=
  ⨆ (member : actor) (_ : member ≠ 1),
    ⁅subgroup ⊓ Subgroup.centralizer {(member : G)}, actor⁆

theorem repeated_action_commutators_le {G : Type u} [Group G]
    (actor subgroup : Subgroup G) : repeatedActionCommutators actor subgroup ≤ ⁅subgroup, actor⁆ := by
  apply iSup_le
  intro member
  apply iSup_le
  intro _
  exact Subgroup.commutator_mono inf_le_left le_rfl

theorem repeated_action_commutator_generation {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup : Subgroup G)
    (habelian : ∀ first second : actor, first * second = second * first)
    (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 2) (hsolvable : Group.IsSolvable subgroup)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    ⁅subgroup, actor⁆ = repeatedActionCommutators actor subgroup := by
  let generated := repeatedActionCommutators actor subgroup
  let fixed := subgroup ⊓ Subgroup.centralizer (actor : Set G)
  have hpgroup : IsPGroup prime actor := IsPGroup.of_card hcard
  have hfactorNormalizes : ∀ member : actor,
      actor ≤ Subgroup.normalizer (subgroup ⊓ Subgroup.centralizer {(member : G)} : Set G) := by
    intro member
    apply normalizes_inf_of_normalizes_both actor subgroup _ hnormalizes
    apply Subgroup.le_normalizer_iff.mpr
    intro other hother element helement
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hotherMember : Commute other (member : G) :=
      congrArg Subtype.val (habelian ⟨other, hother⟩ member)
    exact (hotherMember.mul_left (Subgroup.mem_centralizer_singleton_iff.mp helement)).mul_left
      hotherMember.inv_left
  have hgeneratedNormalizes : actor ≤ Subgroup.normalizer (generated : Set G) := by
    apply (Subgroup.iInf_normalizer_le_normalizer_iSup _).trans'
    apply le_iInf
    intro member
    apply (Subgroup.iInf_normalizer_le_normalizer_iSup _).trans'
    apply le_iInf
    intro _
    exact Subgroup.normalizer_commutator_ge_right _ _
  have hfixedNormalizes : fixed ≤ Subgroup.normalizer (generated : Set G) := by
    apply (Subgroup.iInf_normalizer_le_normalizer_iSup _).trans'
    apply le_iInf
    intro member
    apply (Subgroup.iInf_normalizer_le_normalizer_iSup _).trans'
    apply le_iInf
    intro _
    apply (Subgroup.normalizer_commutator_ge_left _ _).trans'
    apply le_inf inf_le_left
    exact inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr member.property))
  have hgeneratedLe : generated ≤ subgroup :=
    (repeated_action_commutators_le actor subgroup).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalizes)
  have hsubgroupFactor : subgroup ≤ generated ⊔ fixed := by
    rw [solvable_centralizer_generation_of_plane prime hprime actor subgroup hpower hcard
      hsolvable hcomplement hnormalizes]
    apply iSup_le
    intro member
    apply iSup_le
    intro hne
    have hfactor := coprime_commutator_centralizer_factorization prime hprime actor
      (subgroup ⊓ Subgroup.centralizer {(member : G)}) hpgroup
      (fun hdiv => hcomplement (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)))
      (hfactorNormalizes member)
    rw [hfactor]
    apply sup_le
    · have hle : ⁅subgroup ⊓ Subgroup.centralizer {(member : G)}, actor⁆ ≤ generated :=
        le_iSup_of_le member (le_iSup_of_le hne le_rfl)
      exact hle.trans le_sup_left
    · exact (inf_le_inf inf_le_left le_rfl).trans le_sup_right
  have hsubgroupNormalizes : subgroup ≤ Subgroup.normalizer (generated : Set G) :=
    hsubgroupFactor.trans (sup_le Subgroup.le_normalizer hfixedNormalizes)
  apply le_antisymm ?_ (repeated_action_commutators_le actor subgroup)
  apply Subgroup.commutator_le.mpr
  intro element helement member hmember
  obtain ⟨first, hfirst, second, hsecond, hproduct⟩ := normalized_sup_factorization
    generated fixed hfixedNormalizes element (hsubgroupFactor helement)
  have hsecondCommutes : Commute second member :=
    (Subgroup.mem_centralizer_iff.mp hsecond.2 member hmember).symm
  rw [← hproduct, commutatorElement_def]
  have hcommutator : ⁅first, member⁆ ∈ generated :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hgeneratedNormalizes
      (Subgroup.commutator_mem_commutator hfirst hmember)
  simpa only [commutatorElement_def, mul_inv_rev, mul_assoc,
    hsecondCommutes.eq, mul_inv_cancel_left, mul_inv_cancel_right] using hcommutator

end CFSG.RankThreeEvenClassification.Helpers
