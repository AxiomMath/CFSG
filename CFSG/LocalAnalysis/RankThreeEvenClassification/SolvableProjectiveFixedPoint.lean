module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryProjectiveOrder
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ProjectivePrimePairTriviality
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeNormalFixedSets

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

set_option maxHeartbeats 600000 in
theorem solvable_prime_generated_projective_plane_fixed_point {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) [CharP field prime]
    (subgroup : Subgroup (space ≃ₗ[field] space)) [Finite subgroup]
    (projectiveSubgroup : Subgroup ((linearProjectiveAction field space).comp subgroup.subtype).range)
    [Group.IsSolvable projectiveSubgroup]
    (halternative : 5 ≤ prime ∨ Odd (Nat.card projectiveSubgroup))
    (hgenerated : Subgroup.closure {member : projectiveSubgroup | ∃ exponent : ℕ,
      member ^ (prime ^ exponent) = 1} = ⊤) :
    ∃ point : Projectivization field space,
      ∀ member : projectiveSubgroup, (member : Equiv.Perm (Projectivization field space)) point = point := by
  classical
  let projectiveAction := (linearProjectiveAction field space).comp subgroup.subtype
  have : Finite projectiveAction.range := Finite.of_surjective projectiveAction.rangeRestrict
    projectiveAction.rangeRestrict_surjective
  let action : projectiveSubgroup →* Equiv.Perm (Projectivization field space) :=
    projectiveAction.range.subtype.comp projectiveSubgroup.subtype
  have : Nontrivial space := Module.finrank_pos_iff.mp (hdimension ▸ (by omega : 0 < 2))
  by_cases htrivial : Subsingleton projectiveSubgroup
  · have : Subsingleton projectiveSubgroup := htrivial
    obtain ⟨vector, hvectorNe⟩ := exists_ne (0 : space)
    refine ⟨Projectivization.mk field vector hvectorNe, ?_⟩
    intro member
    have heq : member = 1 := Subsingleton.elim member 1
    rw [heq]
    rfl
  have : Nontrivial projectiveSubgroup := not_subsingleton_iff_nontrivial.mp htrivial
  obtain ⟨normal, hminimal⟩ := exists_minimal_nontrivial_normal (G := projectiveSubgroup)
  have : normal.Normal := hminimal.1.1
  have : Nontrivial normal := (Subgroup.nontrivial_iff_ne_bot normal).mpr hminimal.1.2
  obtain ⟨normalPrime, hnormalPrime, helementary, dimension, _, hnormalCard⟩ :=
    minimal_normal_solvable_elementary normal hminimal inferInstance
  have hnormalComm : ∀ first second : normal, first * second = second * first :=
    isMulCommutative_iff.mp helementary.1
  have hnormalPower : ∀ member : normal, member ^ normalPrime = 1 := by
    intro member
    apply Subtype.ext
    exact helementary.2 member member.property
  obtain ⟨generator, hgeneratorNe⟩ := exists_ne (1 : normal)
  have hgeneratorAmbientNe :
      ((generator : projectiveSubgroup) : projectiveAction.range) ≠ 1 := by
    intro heq
    exact hgeneratorNe (Subtype.ext (Subtype.ext heq))
  have hgeneratorPower :
      ((generator : projectiveSubgroup) : projectiveAction.range) ^ (normalPrime ^ 1) = 1 := by
    rw [pow_one]
    have heq := congrArg (projectiveSubgroup.subtype.comp normal.subtype) (hnormalPower generator)
    rw [map_pow, map_one] at heq
    exact heq
  by_cases hsame : normalPrime = prime
  · rw [hsame] at hgeneratorPower
    obtain ⟨point, hpoint, hunique⟩ := projective_pElement_plane_has_unique_fixed_point hdimension
      prime hprime subgroup generator hgeneratorAmbientNe 1 hgeneratorPower
    have hcommon : ∀ member : normal, action member point = point := by
      intro member
      apply hunique
      have hcommute : action (generator : projectiveSubgroup) * action (member : projectiveSubgroup) =
          action (member : projectiveSubgroup) * action (generator : projectiveSubgroup) := by
        rw [← map_mul, ← map_mul]
        exact congrArg (action.comp normal.subtype) (hnormalComm generator member)
      have heq := congrArg (fun permutation : Equiv.Perm (Projectivization field space) => permutation point) hcommute
      change action (generator : projectiveSubgroup) (action (member : projectiveSubgroup) point) =
        action (member : projectiveSubgroup) (action (generator : projectiveSubgroup) point) at heq
      exact heq.trans (congrArg (action (member : projectiveSubgroup)) hpoint)
    have hcommonUnique : ∀ other : Projectivization field space,
        (∀ member : normal, action member other = other) → other = point := by
      intro other hother
      exact hunique other (hother generator)
    exact ⟨point, normal_permutation_unique_common_fixed_point_global action normal point hcommon hcommonUnique⟩
  let normalImage := normal.map projectiveSubgroup.subtype
  let normalEquiv := normal.equivMapOfInjective projectiveSubgroup.subtype Subtype.val_injective
  have : Nontrivial normalImage := normalEquiv.injective.nontrivial
  have hnormalImageComm : ∀ first second : normalImage, first * second = second * first := by
    intro first second
    obtain ⟨firstPreimage, rfl⟩ := normalEquiv.surjective first
    obtain ⟨secondPreimage, rfl⟩ := normalEquiv.surjective second
    rw [← map_mul, ← map_mul, hnormalComm]
  have hnormalImagePower : ∀ member : normalImage, member ^ normalPrime = 1 := by
    intro member
    obtain ⟨preimage, rfl⟩ := normalEquiv.surjective member
    rw [← map_pow, hnormalPower, map_one]
  have hnormalOrder := elementary_projective_coprime_plane_order hdimension prime normalPrime
    hprime hnormalPrime (Ne.symm hsame) subgroup normalImage hnormalImageComm hnormalImagePower
  rw [← Nat.card_congr normalEquiv.toEquiv] at hnormalOrder
  obtain ⟨first, second, hpointsNe, hfixed⟩ := projective_coprime_pElement_plane_has_fixed_pair
    hdimension prime normalPrime hprime hnormalPrime (Ne.symm hsame) subgroup generator
      hgeneratorAmbientNe 1 hgeneratorPower
  rcases hnormalOrder with hcyclic | ⟨hnormalTwo, hnormalFour⟩
  · exact False.elim (projective_prime_generated_plane_cannot_preserve_pair hdimension prime hprime hodd
      subgroup projectiveSubgroup hgenerated first second hpointsNe
        (normal_prime_card_fixed_pair_invariant action normal normalPrime hnormalPrime hcyclic
          generator hgeneratorNe first second hfixed))
  · have hlarge : 5 ≤ prime := by
      rcases halternative with hlarge | hoddOrder
      · exact hlarge
      · have hdivides := normal.card_subgroup_dvd_card
        rw [hnormalFour] at hdivides
        exact False.elim (hoddOrder.not_two_dvd_nat (dvd_trans (by decide : 2 ∣ 4) hdivides))
    have hcentralizes := normal_small_card_prime_generated_centralizes normal prime hprime
      (by rw [hnormalFour]; omega) hgenerated
    have hpreserves : ∀ member : projectiveSubgroup, ∀ point : Projectivization field space,
        action member point ∈ ({first, second} : Set (Projectivization field space)) ↔
          point ∈ ({first, second} : Set (Projectivization field space)) := by
      intro member
      apply commuting_permutation_preserves_fixed_pair (action generator) (action member) _ first second hfixed
      change action (generator : projectiveSubgroup) * action member =
        action member * action (generator : projectiveSubgroup)
      rw [← map_mul, ← map_mul, hcentralizes member generator]
    exact False.elim (projective_prime_generated_plane_cannot_preserve_pair hdimension prime hprime hodd
      subgroup projectiveSubgroup hgenerated first second hpointsNe hpreserves)

end CFSG.RankThreeEvenClassification.Helpers
