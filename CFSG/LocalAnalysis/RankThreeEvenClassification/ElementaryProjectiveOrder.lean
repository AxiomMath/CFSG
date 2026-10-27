module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeProjectiveFixedPoints
public import CFSG.LocalAnalysis.RankThreeEvenClassification.UnitRootCardBounds
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PairPermutationActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem elementary_projective_coprime_plane_order {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (characteristic prime : ℕ) (hcharacteristic : characteristic.Prime) (hprime : prime.Prime)
    (hdistinct : characteristic ≠ prime) [CharP field characteristic]
    (subgroup : Subgroup (space ≃ₗ[field] space)) [Finite subgroup]
    (projectiveSubgroup : Subgroup ((linearProjectiveAction field space).comp subgroup.subtype).range)
    [Nontrivial projectiveSubgroup]
    (hcommutative : ∀ first second : projectiveSubgroup, first * second = second * first)
    (hpower : ∀ member : projectiveSubgroup, member ^ prime = 1) :
    Nat.card projectiveSubgroup = prime ∨ prime = 2 ∧ Nat.card projectiveSubgroup = 4 := by
  classical
  have : Fact prime.Prime := ⟨hprime⟩
  let projectiveAction := (linearProjectiveAction field space).comp subgroup.subtype
  have : Finite projectiveAction.range := Finite.of_surjective projectiveAction.rangeRestrict
    projectiveAction.rangeRestrict_surjective
  have hpGroup : IsPGroup prime projectiveSubgroup := by
    apply IsPGroup.of_exponent_dvd_pow (n := 1)
    rw [pow_one]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hpower
  obtain ⟨member, hmemberNe⟩ := exists_ne (1 : projectiveSubgroup)
  have hmemberAmbientNe : (member : ((linearProjectiveAction field space).comp subgroup.subtype).range) ≠ 1 := by
    intro heq
    exact hmemberNe (Subtype.ext heq)
  have hmemberAmbientPower :
      (member : ((linearProjectiveAction field space).comp subgroup.subtype).range) ^ (prime ^ 1) = 1 := by
    have heq := congrArg projectiveSubgroup.subtype (hpower member)
    rw [map_pow, map_one] at heq
    change (member : ((linearProjectiveAction field space).comp subgroup.subtype).range) ^ prime = 1 at heq
    rw [pow_one]
    exact heq
  obtain ⟨first, second, hpointsNe, hfixed⟩ := projective_coprime_pElement_plane_has_fixed_pair
    hdimension characteristic prime hcharacteristic hprime hdistinct subgroup member
      hmemberAmbientNe 1 hmemberAmbientPower
  let action : projectiveSubgroup →* Equiv.Perm (Projectivization field space) :=
    ((linearProjectiveAction field space).comp subgroup.subtype).range.subtype.comp projectiveSubgroup.subtype
  have hpreserves : ∀ conjugator : projectiveSubgroup, ∀ point : Projectivization field space,
      action conjugator point ∈ ({first, second} : Set (Projectivization field space)) ↔
        point ∈ ({first, second} : Set (Projectivization field space)) := by
    intro conjugator
    apply commuting_permutation_preserves_fixed_pair (action member) (action conjugator) _ first second hfixed
    change action member * action conjugator = action conjugator * action member
    rw [← map_mul, ← map_mul, hcommutative]
  let pairAction := pairPermutationAction action first second hpreserves
  let kernelImage := pairAction.ker.map projectiveSubgroup.subtype
  let kernelEquiv := pairAction.ker.equivMapOfInjective projectiveSubgroup.subtype Subtype.val_injective
  have hkernelFixed : ∀ kernelMember : kernelImage,
      (kernelMember : Equiv.Perm (Projectivization field space)) first = first ∧
        (kernelMember : Equiv.Perm (Projectivization field space)) second = second := by
    intro kernelMember
    obtain ⟨preimage, hpreimage, heq⟩ := kernelMember.property
    have hpreimageFixed := (pairPermutationAction_mem_kernel_iff action first second hpreserves preimage).mp hpreimage
    change ((kernelMember : ((linearProjectiveAction field space).comp subgroup.subtype).range) :
      Equiv.Perm (Projectivization field space)) first = first ∧ _
    rw [← heq]
    exact hpreimageFixed
  have hkernelImagePower : ∀ kernelMember : kernelImage, kernelMember ^ prime = 1 := by
    intro kernelMember
    obtain ⟨preimage, _, heq⟩ := kernelMember.property
    apply Subtype.ext
    change (kernelMember : projectiveAction.range) ^ prime = 1
    rw [← heq, ← map_pow, hpower, map_one]
  have hkernelBound : Nat.card pairAction.ker ≤ prime := by
    rw [Nat.card_congr kernelEquiv.toEquiv]
    exact projective_pointwise_pair_exponent_card_le hdimension subgroup kernelImage first second
      hpointsNe hkernelFixed prime hprime.pos hkernelImagePower
  have hmemberKernel : member ∈ pairAction.ker := by
    apply (pairPermutationAction_mem_kernel_iff action first second hpreserves member).mpr
    exact ⟨(hfixed first).mpr (Or.inl rfl), (hfixed second).mpr (Or.inr rfl)⟩
  have : Nontrivial pairAction.ker := by
    apply nontrivial_of_ne (⟨member, hmemberKernel⟩ : pairAction.ker) 1
    intro heq
    exact hmemberNe (congrArg Subtype.val heq)
  have hkernelCard : Nat.card pairAction.ker = prime := by
    rcases (hpGroup.to_subgroup pairAction.ker).card_eq_or_dvd with hone | hdivides
    · have hsubsingleton := (Nat.card_eq_one_iff_unique.mp hone).1
      exact False.elim (hmemberNe (congrArg Subtype.val
        (hsubsingleton.elim (⟨member, hmemberKernel⟩ : pairAction.ker) 1)))
    · exact Nat.le_antisymm hkernelBound (Nat.le_of_dvd (Nat.card_pos) hdivides)
  have hrangeDivides : Nat.card pairAction.range ∣ 2 :=
    pairPermutationAction_range_card_dvd_two action first second hpointsNe hpreserves
  have hcard : Nat.card projectiveSubgroup = Nat.card pairAction.range * prime := by
    rw [pairAction.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange pairAction).toEquiv, hkernelCard]
  rcases Nat.prime_two.eq_one_or_self_of_dvd (Nat.card pairAction.range) hrangeDivides with hone | htwo
  · left
    simpa only [hone, one_mul] using hcard
  · right
    have hprimeTwo : prime = 2 := by
      have hrangeGroup := hpGroup.of_surjective pairAction.rangeRestrict pairAction.rangeRestrict_surjective
      rcases hrangeGroup.card_eq_or_dvd with hone | hdivides
      · omega
      · rw [htwo] at hdivides
        exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hdivides
    exact ⟨hprimeTwo, by simpa only [htwo, hprimeTwo] using hcard⟩

end CFSG.RankThreeEvenClassification.Helpers
