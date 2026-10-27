module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3OddCoreAll

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

open CFSG.ComponentClassification.CatalogueBOddQuadratic in
theorem exists_pow_two_pow_eq_one_of_commute [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) {ν : V ≃ₗ[K] V}
    (hν : ν ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ g ∈ elementaryGroup Q, ν * g = g * ν) : ∃ e : ℕ, ν ^ (2 ^ e) = 1 := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hodd3 : Odd (Nat.card K) := by rw [hK]; decide
  by_cases hd : Module.finrank K V ≤ 2
  · exact ⟨4, pow_sixteen_eq_one_of_finrank_le_two hK hQ hd hν⟩
  push Not at hd
  have hA : HasAnisoPerp Q := hasAnisoPerp_of_three_le_finrank hQ (by omega)
  obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_three_le hodd3 Q hQ (by omega)
  obtain ⟨P, -⟩ := exists_hypPair hQ hvQ hv0
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two]
  exact mul_self_eq_one_of_commute_eichler h2 hQ hA P hν fun u w _ _ =>
    hcomm _ (eichler_mem_elementaryGroup Q u w)

end CFSG.ClassicalGroups.Orthogonal.Small
