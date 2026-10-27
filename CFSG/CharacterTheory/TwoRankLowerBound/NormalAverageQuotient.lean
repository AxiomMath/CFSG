module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuotientGroupAlgebraEndomorphisms
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalSubgroupAverage
public import CFSG.CharacterTheory.TwoRankLowerBound.PGroupAlgebraUnits

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem normalSubgroupAverage_single_eq_of_quotient_eq {ring source target : Type*}
    [CommRing ring] [Group source] [Fintype source] [Group target]
    (quotient : source →* target) [Fintype quotient.ker] (cardUnit : ringˣ)
    (left right : source) (hequal : quotient left = quotient right) :
    normalSubgroupAverage quotient.ker cardUnit * MonoidAlgebra.single left 1 =
      normalSubgroupAverage quotient.ker cardUnit * MonoidAlgebra.single right 1 := by
  let difference : quotient.ker := ⟨right * left⁻¹, by
    change quotient (right * left⁻¹) = 1
    rw [map_mul, map_inv, hequal, mul_inv_cancel]⟩
  have hright : right = difference.val * left := by
    dsimp only [difference]
    group
  rw [hright, ← show MonoidAlgebra.single difference.val 1 *
    MonoidAlgebra.single left 1 = (MonoidAlgebra.single (difference.val * left) 1 :
      MonoidAlgebra ring source) by simp only [MonoidAlgebra.single_mul_single, one_mul], ← mul_assoc,
    normalSubgroupAverage_mul_single quotient.ker cardUnit difference]

noncomputable def normalAverageQuotientSection {ring source target : Type*}
    [CommRing ring] [Group source] [Fintype source] [Group target]
    (quotient : source →* target) (hsurjective : Function.Surjective quotient)
    [Fintype quotient.ker] (cardUnit : ringˣ) :
    MonoidAlgebra ring target →ₗ[ring] MonoidAlgebra ring source :=
  (MonoidAlgebra.basis target ring).constr ring (fun element =>
    normalSubgroupAverage quotient.ker cardUnit *
      MonoidAlgebra.single (Classical.choose (hsurjective element)) 1)

theorem normalAverageQuotientSection_single {ring source target : Type*}
    [CommRing ring] [Group source] [Fintype source] [Group target]
    (quotient : source →* target) (hsurjective : Function.Surjective quotient)
    [Fintype quotient.ker] (cardUnit : ringˣ) (element : target) :
    normalAverageQuotientSection quotient hsurjective cardUnit (MonoidAlgebra.single element 1) =
      normalSubgroupAverage quotient.ker cardUnit *
        MonoidAlgebra.single (Classical.choose (hsurjective element)) 1 := by
  exact (MonoidAlgebra.basis target ring).constr_basis ring _ element

theorem normalAverageQuotientSection_mapDomain {ring source target : Type*}
    [CommRing ring] [Group source] [Fintype source] [Group target]
    (quotient : source →* target) (hsurjective : Function.Surjective quotient)
    [Fintype quotient.ker] (cardUnit : ringˣ) (value : MonoidAlgebra ring source) :
    normalAverageQuotientSection quotient hsurjective cardUnit
        (MonoidAlgebra.mapDomainRingHom ring quotient value) =
      normalSubgroupAverage quotient.ker cardUnit * value := by
  have hequal : (normalAverageQuotientSection quotient hsurjective cardUnit).comp
      (MonoidAlgebra.mapDomainAlgHom ring ring quotient).toLinearMap =
        Algebra.lmul ring (MonoidAlgebra ring source) (normalSubgroupAverage quotient.ker cardUnit) := by
    apply (MonoidAlgebra.basis source ring).ext
    intro element
    change normalAverageQuotientSection quotient hsurjective cardUnit
      (MonoidAlgebra.mapDomainRingHom ring quotient (MonoidAlgebra.single element 1)) = _
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      normalAverageQuotientSection_single]
    exact normalSubgroupAverage_single_eq_of_quotient_eq quotient cardUnit _ element
      (Classical.choose_spec (hsurjective (quotient element)))
  exact congrArg (fun operator : Module.End ring (MonoidAlgebra ring source) => operator value) hequal

theorem normalSubgroupAverage_mapDomain {ring source target : Type*}
    [CommRing ring] [Group source] [Fintype source] [Group target]
    (quotient : source →* target) [Fintype quotient.ker] (cardUnit : ringˣ)
    (hcard : (cardUnit : ring) = Nat.card quotient.ker) :
    MonoidAlgebra.mapDomainRingHom ring quotient (normalSubgroupAverage quotient.ker cardUnit) = 1 := by
  change MonoidAlgebra.mapDomainAlgHom ring ring quotient (normalSubgroupAverage quotient.ker cardUnit) = 1
  have hkernel : ∀ element : quotient.ker, quotient element.val = 1 :=
    fun element => MonoidHom.mem_ker.mp element.property
  unfold normalSubgroupAverage
  change MonoidAlgebra.mapDomainAlgHom ring ring quotient
    (((cardUnit⁻¹ : ringˣ) : ring) • ∑ element : quotient.ker, MonoidAlgebra.single element.val 1) = 1
  rw [map_smul, map_sum]
  simp only [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single, hkernel,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ring, ← hcard]
  change ((cardUnit⁻¹ : ringˣ) : ring) • ((cardUnit : ring) • (1 : MonoidAlgebra ring target)) = 1
  rw [smul_smul, Units.inv_mul, one_smul]

theorem normalAverageQuotientSection_rightInverse {ring source target : Type*}
    [CommRing ring] [Group source] [Fintype source] [Group target]
    (quotient : source →* target) (hsurjective : Function.Surjective quotient)
    [Fintype quotient.ker] (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker) :
    Function.RightInverse (normalAverageQuotientSection quotient hsurjective cardUnit)
      (MonoidAlgebra.mapDomainRingHom ring quotient) := by
  intro value
  obtain ⟨preimage, rfl⟩ := groupAlgebra_mapDomain_surjective quotient hsurjective value
  rw [normalAverageQuotientSection_mapDomain, map_mul, normalSubgroupAverage_mapDomain quotient cardUnit hcard,
    one_mul]

theorem normal_average_idempotent_eq_zero_or_average {ring source target : Type*}
    [CommRing ring] [IsLocalRing ring] [Group source] [Fintype source] [Group target] [Finite target]
    (quotient : source →* target) (hsurjective : Function.Surjective quotient)
    [Fintype quotient.ker] (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime target) (value : MonoidAlgebra ring source)
    (hidempotent : IsIdempotentElem value)
    (hsupport : normalSubgroupAverage quotient.ker cardUnit * value = value) :
    value = 0 ∨ value = normalSubgroupAverage quotient.ker cardUnit := by
  rcases local_p_group_algebra_idempotent_eq_zero_or_one prime hgroup
    (MonoidAlgebra.mapDomainRingHom ring quotient value)
    (hidempotent.map (MonoidAlgebra.mapDomainRingHom ring quotient)) with hzero | hone
  · left
    rw [← hsupport, ← normalAverageQuotientSection_mapDomain quotient hsurjective cardUnit,
      hzero, map_zero]
  · right
    have haverage := normalAverageQuotientSection_mapDomain quotient hsurjective cardUnit
      (normalSubgroupAverage quotient.ker cardUnit)
    rw [normalSubgroupAverage_mapDomain quotient cardUnit hcard,
      (normalSubgroupAverage_idempotent quotient.ker cardUnit hcard).eq] at haverage
    rw [← hsupport, ← normalAverageQuotientSection_mapDomain quotient hsurjective cardUnit, hone, haverage]

end CFSG.TwoRankLowerBound.Helpers
