module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticLinearIdentities
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableProjectiveFixedPoint
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LinearPairInvariantSubspaces

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

set_option maxHeartbeats 500000 in
theorem solvable_quadratic_plane_common_fixed_vector {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) [CharP field prime]
    (first second : space ≃ₗ[field] space)
    (hfirst : ((first : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (hsecond : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0)
    [Finite (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))]
    [Group.IsSolvable (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))]
    (halternative : 5 ≤ prime ∨
      Odd (Nat.card (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space)))) :
    ∃ vector : space, vector ≠ 0 ∧ first vector = vector ∧ second vector = vector := by
  classical
  let pair := Subgroup.zpowers first ⊔ Subgroup.zpowers second
  let action := (linearProjectiveAction field space).comp pair.subtype
  have : Finite action.range := Finite.of_surjective action.rangeRestrict action.rangeRestrict_surjective
  have : Group.IsSolvable action.range :=
    Group.isSolvable_of_surjective (f := action.rangeRestrict) action.rangeRestrict_surjective
  have hfirstPower := quadratic_linear_pow_prime_eq_one prime first hfirst
  have hsecondPower := quadratic_linear_pow_prime_eq_one prime second hsecond
  have hpairGenerated := pair_prime_power_generated prime first second
    ⟨1, by simpa only [pow_one] using hfirstPower⟩ ⟨1, by simpa only [pow_one] using hsecondPower⟩
  let projection : pair →* (⊤ : Subgroup action.range) :=
    Subgroup.topEquiv.symm.toMonoidHom.comp action.rangeRestrict
  have hprojectionSurjective : Function.Surjective projection :=
    Subgroup.topEquiv.symm.surjective.comp action.rangeRestrict_surjective
  have hgenerated := prime_power_generated_of_surjective prime projection hprojectionSurjective hpairGenerated
  have hprojectiveAlternative : 5 ≤ prime ∨ Odd (Nat.card (⊤ : Subgroup action.range)) := by
    rcases halternative with hlarge | hoddCard
    · exact Or.inl hlarge
    · right
      rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
      exact odd_card_range_of_odd_domain action hoddCard
  obtain ⟨point, hpoint⟩ := solvable_prime_generated_projective_plane_fixed_point hdimension prime hprime hodd
    pair (⊤ : Subgroup action.range) hprojectiveAlternative hgenerated
  let firstMember : pair := ⟨first, Subgroup.mem_sup_left (Subgroup.mem_zpowers first)⟩
  let secondMember : pair := ⟨second, Subgroup.mem_sup_right (Subgroup.mem_zpowers second)⟩
  have hfirstProjective : linearProjectiveAction field space first point = point := hpoint (projection firstMember)
  have hsecondProjective : linearProjectiveAction field space second point = point := hpoint (projection secondMember)
  have hfirstFixed : first point.rep = point.rep := by
    apply (linear_pElement_fixed_projective_iff_fixed_vector prime hprime first 1
      (by simpa only [pow_one] using hfirstPower) point.rep point.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using hfirstProjective
  have hsecondFixed : second point.rep = point.rep := by
    apply (linear_pElement_fixed_projective_iff_fixed_vector prime hprime second 1
      (by simpa only [pow_one] using hsecondPower) point.rep point.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using hsecondProjective
  exact ⟨point.rep, point.rep_nonzero, hfirstFixed, hsecondFixed⟩

end CFSG.RankThreeEvenClassification.Helpers
