module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.LinearPairStability
public import CFSG.LocalAnalysis.RankThreeEvenClassification.AlgebraicClosureActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

set_option maxHeartbeats 500000 in
theorem solvable_linear_prime_stable_action {actor : Type u} {field : Type v} {space : Type w}
    [Group actor] [Finite actor] [Group.IsSolvable actor]
    [Field field] [AddCommGroup space] [Module field space] [FiniteDimensional field space]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) [CharP field prime]
    (action : actor →* (space ≃ₗ[field] space))
    (halternative : 5 ≤ prime ∨ Odd (Nat.card actor)) : LinearPrimeStableAction prime action := by
  have : Finite action.range := Finite.of_surjective action.rangeRestrict action.rangeRestrict_surjective
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
  let equivalence := (internalPair.equivMapOfInjective action.range.subtype action.range.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  have : Finite ambientPair := Finite.of_surjective equivalence equivalence.surjective
  have : Group.IsSolvable ambientPair :=
    Group.isSolvable_of_surjective (f := equivalence.toMonoidHom) equivalence.surjective
  have hpairAlternative : 5 ≤ prime ∨ Odd (Nat.card ambientPair) := by
    rcases halternative with hlarge | hoddOrder
    · exact Or.inl hlarge
    · right
      rw [← Nat.card_congr equivalence.toEquiv]
      exact (odd_card_range_of_odd_domain action hoddOrder).of_dvd_nat internalPair.card_subgroup_dvd_card
  have hsecondQuadratic : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0 :=
    quadratic_linear_conjugate (action member) conjugator hquadratic
  have hambientGroup : IsPGroup prime ambientPair := solvable_quadratic_pair_isPGroup prime hprime hodd
    (first : space ≃ₗ[field] space) (second : space ≃ₗ[field] space) hquadratic hsecondQuadratic hpairAlternative
  change IsPGroup prime internalPair
  exact hambientGroup.of_equiv equivalence.symm

end CFSG.RankThreeEvenClassification.Helpers
