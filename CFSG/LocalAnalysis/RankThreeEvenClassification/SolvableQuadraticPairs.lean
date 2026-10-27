module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.LinearPrimeExtension
public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticInvariantActions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LinearPairImage
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableQuadraticReducibility

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

set_option maxHeartbeats 700000 in
theorem solvable_quadratic_pair_isPGroup_algebraically_closed {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) [CharP field prime]
    (first second : space ≃ₗ[field] space)
    (hfirst : ((first : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (hsecond : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0)
    [Finite (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))]
    [Group.IsSolvable (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))]
    (halternative : 5 ≤ prime ∨
      Odd (Nat.card (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space)))) :
    IsPGroup prime (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space)) := by
  classical
  generalize hsize : Module.finrank field space = size
  induction size using Nat.strong_induction_on generalizing space with
  | h size ih =>
    by_cases hzero : size = 0
    · have : Subsingleton space := (Module.finrank_eq_zero_iff_of_free field space).mp (hsize.trans hzero)
      have hfirstOne : first = 1 := by
        apply LinearEquiv.ext
        intro member
        exact Subsingleton.elim _ _
      have hsecondOne : second = 1 := by
        apply LinearEquiv.ext
        intro member
        exact Subsingleton.elim _ _
      rw [hfirstOne, hsecondOne, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
      exact IsPGroup.of_subsingleton prime _
    by_cases hone : size = 1
    · have hdimension : Module.finrank field space = 1 := hsize.trans hone
      have hfirstOne := one_dimensional_linear_pElement_eq_one prime hprime hdimension first 1
        (by simpa only [pow_one] using quadratic_linear_pow_prime_eq_one prime first hfirst)
      have hsecondOne := one_dimensional_linear_pElement_eq_one prime hprime hdimension second 1
        (by simpa only [pow_one] using quadratic_linear_pow_prime_eq_one prime second hsecond)
      rw [hfirstOne, hsecondOne, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
      exact IsPGroup.of_subsingleton prime _
    obtain ⟨subspace, hsubspaceBot, hsubspaceTop, hfirstMap, hsecondMap⟩ :=
      solvable_quadratic_pair_reducible (by rw [hsize]; omega) prime hprime hodd first second hfirst hsecond halternative
    let pair := Subgroup.zpowers first ⊔ Subgroup.zpowers second
    let action := pair.subtype
    have hinvariant : ∀ member : pair, subspace.map (action member : Module.End field space) = subspace :=
      linear_pair_invariant_subspace first second subspace hfirstMap hsecondMap
    let restriction := linearSubspaceAction action subspace hinvariant
    let quotient := linearQuotientAction action subspace hinvariant
    let firstMember : pair := ⟨first, Subgroup.mem_sup_left (Subgroup.mem_zpowers first)⟩
    let secondMember : pair := ⟨second, Subgroup.mem_sup_right (Subgroup.mem_zpowers second)⟩
    have hrestrictionRange := pair_homomorphism_range first second restriction
    have hquotientRange := pair_homomorphism_range first second quotient
    have : Finite restriction.range := Finite.of_surjective restriction.rangeRestrict restriction.rangeRestrict_surjective
    have : Group.IsSolvable restriction.range :=
      Group.isSolvable_of_surjective (f := restriction.rangeRestrict) restriction.rangeRestrict_surjective
    have : Finite quotient.range := Finite.of_surjective quotient.rangeRestrict quotient.rangeRestrict_surjective
    have : Group.IsSolvable quotient.range :=
      Group.isSolvable_of_surjective (f := quotient.rangeRestrict) quotient.rangeRestrict_surjective
    have : Finite (Subgroup.zpowers (restriction firstMember) ⊔ Subgroup.zpowers (restriction secondMember) :
        Subgroup (subspace ≃ₗ[field] subspace)) := by
      rw [← hrestrictionRange]
      infer_instance
    have : Group.IsSolvable (Subgroup.zpowers (restriction firstMember) ⊔ Subgroup.zpowers (restriction secondMember) :
        Subgroup (subspace ≃ₗ[field] subspace)) := by
      rw [← hrestrictionRange]
      infer_instance
    have : Finite (Subgroup.zpowers (quotient firstMember) ⊔ Subgroup.zpowers (quotient secondMember) :
        Subgroup ((space ⧸ subspace) ≃ₗ[field] (space ⧸ subspace))) := by
      rw [← hquotientRange]
      infer_instance
    have : Group.IsSolvable (Subgroup.zpowers (quotient firstMember) ⊔ Subgroup.zpowers (quotient secondMember) :
        Subgroup ((space ⧸ subspace) ≃ₗ[field] (space ⧸ subspace))) := by
      rw [← hquotientRange]
      infer_instance
    have hrestrictionAlternative : 5 ≤ prime ∨ Odd (Nat.card
        (Subgroup.zpowers (restriction firstMember) ⊔ Subgroup.zpowers (restriction secondMember) :
          Subgroup (subspace ≃ₗ[field] subspace))) := by
      rw [← hrestrictionRange]
      exact halternative.imp_right (odd_card_range_of_odd_domain restriction)
    have hquotientAlternative : 5 ≤ prime ∨ Odd (Nat.card
        (Subgroup.zpowers (quotient firstMember) ⊔ Subgroup.zpowers (quotient secondMember) :
          Subgroup ((space ⧸ subspace) ≃ₗ[field] (space ⧸ subspace)))) := by
      rw [← hquotientRange]
      exact halternative.imp_right (odd_card_range_of_odd_domain quotient)
    have hsubspaceSmall : Module.finrank field subspace < size := by
      rw [← hsize]
      exact Submodule.finrank_lt hsubspaceTop
    have hquotientSmall : Module.finrank field (space ⧸ subspace) < size := by
      have hadd := subspace.finrank_quotient_add_finrank
      have hpositive : Module.finrank field subspace ≠ 0 :=
        fun heq => hsubspaceBot (Submodule.finrank_eq_zero.mp heq)
      rw [hsize] at hadd
      omega
    have hrestrictionGroup : IsPGroup prime restriction.range := by
      rw [hrestrictionRange]
      exact ih (Module.finrank field subspace) hsubspaceSmall (restriction firstMember) (restriction secondMember)
        (quadratic_linear_subspace_action action subspace hinvariant firstMember hfirst)
        (quadratic_linear_subspace_action action subspace hinvariant secondMember hsecond) hrestrictionAlternative rfl
    have hquotientGroup : IsPGroup prime quotient.range := by
      rw [hquotientRange]
      exact ih (Module.finrank field (space ⧸ subspace)) hquotientSmall (quotient firstMember) (quotient secondMember)
        (quadratic_linear_quotient_action action subspace hinvariant firstMember hfirst)
        (quadratic_linear_quotient_action action subspace hinvariant secondMember hsecond) hquotientAlternative rfl
    exact faithful_linear_pGroup_of_subspace_quotient prime hprime action Subtype.val_injective
      subspace hinvariant hrestrictionGroup hquotientGroup

end CFSG.RankThreeEvenClassification.Helpers
