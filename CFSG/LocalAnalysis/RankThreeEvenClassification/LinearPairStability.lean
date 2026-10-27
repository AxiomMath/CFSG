module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryLinearActions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeCorePreimage
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableConjugatePairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticLinearIdentities

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

theorem linearPrimeStableAction_of_solvable_conjugate_pairs
    {actor : Type u} {field : Type v} {space : Type w}
    [Group actor] [Finite actor] [Group.IsSolvable actor]
    [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) (hprime : prime.Prime) (action : actor →* (space ≃ₗ[field] space))
    (hpairs : ∀ member : actor, ((action member : Module.End field space) - LinearMap.id) ^ 2 = 0 →
      PrimeConjugatePairs prime (action.rangeRestrict member)) :
    LinearPrimeStableAction prime action := by
  have : Finite action.range := Finite.of_surjective action.rangeRestrict action.rangeRestrict_surjective
  have : Group.IsSolvable action.range :=
    Group.isSolvable_of_surjective (f := action.rangeRestrict) action.rangeRestrict_surjective
  intro member hquadratic
  rw [primeCore_quotient_preimage_eq_range_preimage]
  exact solvable_conjugate_pair_mem_primeCore prime hprime (action.rangeRestrict member)
    (hpairs member hquadratic)

theorem linearPrimeStableAction_of_solvable_quadratic_pairs
    {actor : Type u} {field : Type v} {space : Type w}
    [Group actor] [Finite actor] [Group.IsSolvable actor]
    [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) (hprime : prime.Prime) (action : actor →* (space ≃ₗ[field] space))
    (hpair : ∀ first second : space ≃ₗ[field] space,
      ((first : Module.End field space) - LinearMap.id) ^ 2 = 0 →
      ((second : Module.End field space) - LinearMap.id) ^ 2 = 0 →
      Group.IsSolvable (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space)) →
      IsPGroup prime (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))) :
    LinearPrimeStableAction prime action := by
  have : Group.IsSolvable action.range :=
    Group.isSolvable_of_surjective (f := action.rangeRestrict) action.rangeRestrict_surjective
  apply linearPrimeStableAction_of_solvable_conjugate_pairs prime hprime action
  intro member hquadratic conjugator
  let first := action.rangeRestrict member
  let second := conjugator⁻¹ * first * conjugator
  let internalPair := Subgroup.zpowers first ⊔ Subgroup.zpowers second
  let ambientPair := Subgroup.zpowers (first : space ≃ₗ[field] space) ⊔
    Subgroup.zpowers (second : space ≃ₗ[field] space)
  have hmap : internalPair.map action.range.subtype = ambientPair := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hambientSolvable : Group.IsSolvable ambientPair := by
    have : Group.IsSolvable internalPair := inferInstance
    have hequivalence := (internalPair.equivMapOfInjective action.range.subtype action.range.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
    exact Group.isSolvable_of_surjective (f := hequivalence.toMonoidHom) hequivalence.surjective
  have hsecondQuadratic : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0 :=
    quadratic_linear_conjugate (action member) conjugator hquadratic
  have hambientPGroup := hpair first second hquadratic hsecondQuadratic hambientSolvable
  have hpreimage := hambientPGroup.comap_of_injective action.range.subtype action.range.subtype_injective
  apply hpreimage.to_le
  apply Subgroup.map_le_iff_le_comap.mp
  exact hmap.le

end CFSG.RankThreeEvenClassification.Helpers
