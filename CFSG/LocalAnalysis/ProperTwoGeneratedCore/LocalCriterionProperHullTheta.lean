module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementTheta

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_theta_eq_iterated_core (D : Subgroup G) (p : ℕ) (hp : p.Prime) :
    minimalLocalFailurePairConfinementTheta p D =
      (pPrimeCore p ((CFSG.oddCore D).map D.subtype)).map
        ((CFSG.oddCore D).map D.subtype).subtype :=
  generatedPairGrowth_ambient_canonical_core_eq D hp

theorem properHull_theta_inf_subgroup_le
    (p : ℕ) (hp : p.Prime) (D E : Subgroup G) (hED : E ≤ D) :
    minimalLocalFailurePairConfinementTheta p D ⊓ E ≤
      minimalLocalFailurePairConfinementTheta p E := by
  let C := minimalLocalFailurePairConfinementTheta p D
  have hEN : E ≤ Subgroup.normalizer ((C ⊓ E : Subgroup G) : Set G) :=
    (le_inf (hED.trans (Subgroup.le_normalizer.trans (pairConfinement_theta_normalizer p D)))
      Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hn : ((C ⊓ E : Subgroup G).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hEN
  obtain ⟨hodd, hcop⟩ := pairConfinement_theta_order p hp D
  exact pairConfinement_theta_maximal p hp E (C ⊓ E) inf_le_right hn
    (hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    (hcop.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left))

theorem properHull_theta_inf_subgroup_eq
    (p : ℕ) (hp : p.Prime) (D E : Subgroup G) (hED : E ≤ D)
    (hcore : minimalLocalFailurePairConfinementTheta p E ≤
      minimalLocalFailurePairConfinementTheta p D) :
    minimalLocalFailurePairConfinementTheta p D ⊓ E =
      minimalLocalFailurePairConfinementTheta p E :=
  le_antisymm (properHull_theta_inf_subgroup_le p hp D E hED)
    (le_inf hcore (pairConfinement_theta_le p E))

theorem properHull_pGroup_inf_theta_eq_bot
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (D E Q : Subgroup G)
    (hED : E ≤ D) (hQ : IsPGroup q Q)
    (hQC : Q ≤ minimalLocalFailurePairConfinementTheta p D)
    (hqE : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p E)) :
    Q ⊓ E = ⊥ := by
  let : Fact q.Prime := ⟨hq⟩
  have hQE : Q ⊓ E ≤ minimalLocalFailurePairConfinementTheta p E :=
    (inf_le_inf hQC le_rfl).trans (properHull_theta_inf_subgroup_le p hp D E hED)
  apply Subgroup.card_eq_one.mp
  rcases hQ.to_inf_left.card_eq_or_dvd with hcard | hdiv
  · exact hcard
  · exact False.elim (hqE (hdiv.trans (Subgroup.card_dvd_of_le hQE)))

theorem properHull_strict_hall_theta_prime
    (p : ℕ) (hp : p.Prime) (D E : Subgroup G)
    (hstrict : minimalLocalFailurePairConfinementTheta p E <
      minimalLocalFailurePairConfinementTheta p D)
    (hhall : Nat.Coprime (Nat.card (minimalLocalFailurePairConfinementTheta p E))
      ((minimalLocalFailurePairConfinementTheta p E).relIndex
        (minimalLocalFailurePairConfinementTheta p D))) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ≠ p ∧
      q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p D) ∧
      ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p E) := by
  let C := minimalLocalFailurePairConfinementTheta p D
  let V := minimalLocalFailurePairConfinementTheta p E
  have hidx : V.relIndex C ≠ 1 := by
    intro heq
    exact hstrict.not_ge (Subgroup.relIndex_eq_one.mp heq)
  obtain ⟨q, hq, hqidx⟩ := Nat.exists_prime_and_dvd hidx
  have hqC : q ∣ Nat.card C := hqidx.trans (Subgroup.relIndex_dvd_card V C)
  obtain ⟨hodd, hpcop⟩ := pairConfinement_theta_order p hp D
  have hqne : q ≠ p := by
    intro heq
    have hpp : p ∣ Nat.card C := heq ▸ hqC
    exact hp.coprime_iff_not_dvd.mp hpcop hpp
  refine ⟨q, hq, hodd.of_dvd_nat hqC, hqne, hqC, ?_⟩
  intro hqV
  have hqq : Nat.Coprime q q := (hhall.of_dvd_left hqV).of_dvd_right hqidx
  exact hq.ne_one (by simpa only [Nat.Coprime, Nat.gcd_self] using hqq)

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
