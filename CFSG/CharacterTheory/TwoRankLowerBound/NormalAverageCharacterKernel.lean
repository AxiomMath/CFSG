module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalAverageCharacterSupport

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem normalSubgroup_character_constant_degree_trivial {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (subgroup : Subgroup G) [subgroup.Normal]
    [Fintype subgroup] (label : basis.index)
    (hconstant : ∀ element : subgroup, (basis.representation label).character element.val =
      (basis.representation label).character 1) :
    ∀ element : subgroup, (basis.representation label).representation element.val = 1 := by
  let cardUnit : ℂˣ := Units.mk0 (Nat.card subgroup) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hcard : (cardUnit : ℂ) = Nat.card subgroup := rfl
  have hcentral := normalSubgroupAverage_central subgroup cardUnit
  have haction := centralCharacterScalar_action basis (normalSubgroupAverage subgroup cardUnit) hcentral label
  have htrace := congrArg (LinearMap.trace ℂ (basis.representation label).vector) haction
  rw [map_smul, LinearMap.trace_one,
    ← Representation.char_one (basis.representation label).representation] at htrace
  have hleft : LinearMap.trace ℂ (basis.representation label).vector
      ((basis.representation label).representation.asAlgebraHom (normalSubgroupAverage subgroup cardUnit)) =
        (basis.representation label).character 1 := by
    unfold normalSubgroupAverage
    change LinearMap.trace ℂ (basis.representation label).vector
      ((basis.representation label).representation.asAlgebraHom
        (((cardUnit⁻¹ : ℂˣ) : ℂ) • (∑ member : subgroup,
          MonoidAlgebra.single member.val 1 : MonoidAlgebra ℂ G))) = _
    rw [map_smul, map_sum, map_smul, map_sum]
    simp only [Representation.asAlgebraHom_single, one_smul]
    change ((cardUnit⁻¹ : ℂˣ) : ℂ) * ∑ member : subgroup,
      (basis.representation label).character member.val = _
    simp only [hconstant, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, ← hcard]
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hleft] at htrace
  have hscalar : centralCharacterScalar basis (normalSubgroupAverage subgroup cardUnit) label = 1 := by
    apply mul_right_cancel₀ (irreducible_character_degree_ne_zero (basis.representation label)
      (basis.irreducible label))
    exact htrace.symm.trans (one_mul _).symm
  rw [hscalar, one_smul] at haction
  exact (normalSubgroupAverage_action_one_iff subgroup cardUnit hcard (basis.representation label)).mp haction

end CFSG.TwoRankLowerBound.Helpers
