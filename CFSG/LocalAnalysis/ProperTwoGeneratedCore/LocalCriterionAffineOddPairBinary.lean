module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairFourPoint

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Y Ω K : Type*} [Group Y] [Group K] [Finite Ω] [MulAction Y Ω]

theorem elementary_prime_eq_two_of_two_group [Finite K] [Nontrivial K]
    (ℓ : ℕ) (hℓ : ℓ.Prime) [IsElementaryAbelian ℓ K] (hK : IsPGroup 2 K) : ℓ = 2 := by
  let : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨q, hq⟩ := exists_ne (1 : K)
  have hpow : q ^ ℓ = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p ℓ K) q
  have horder : orderOf q = ℓ := orderOf_eq_prime hpow hq
  obtain ⟨n, hn⟩ := hK.exists_orderOf_eq_pow q
  have hdiv : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow (by rw [← hn, horder])
  exact ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left hℓ.ne_one

theorem binary_regular_normal_image_degree_four [Finite Y]
    (hno : ∀ V : Subgroup Y, ¬ IsKleinFour V) (hdegree : 3 ≤ Nat.card Ω)
    (Q : Subgroup ((MulAction.toPermHom Y Ω).range)) [Q.Normal]
    [IsElementaryAbelian 2 Q]
    (hreg : RegularOnEntire (MulAction.toPermHom Y Ω).range Q) :
    Nat.card Ω = 4 := by
  have hnonempty : Nonempty Ω := (Nat.card_pos_iff.mp (show 0 < Nat.card Ω by omega)).1
  obtain ⟨α⟩ := hnonempty
  have hcard := regular_card_eq_degree (MulAction.toPermHom Y Ω).range Q hreg α
  have hbound := normal_elementary_binary_image_card_le_four hno
    (MulAction.toPermHom Y Ω).rangeRestrict
    (MulAction.toPermHom Y Ω).rangeRestrict_surjective Q
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 Q).exists_card_eq
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by omega : 1 < (2 : ℕ))).mp
    simpa [hn] using hbound
  have hnge : 2 ≤ n := by
    by_contra h
    have hnsmall : n = 0 ∨ n = 1 := by omega
    rcases hnsmall with rfl | rfl
    · have hsmall : Nat.card Q = 1 := by simpa using hn
      omega
    · have hsmall : Nat.card Q = 2 := by simpa using hn
      omega
  have hnEq : n = 2 := by omega
  rw [hnEq] at hn
  omega

theorem binary_regular_odd_pair_fixes_every_point [Finite Y]
    (hno : ∀ V : Subgroup Y, ¬ IsKleinFour V) (hdegree : 3 ≤ Nat.card Ω)
    (Q : Subgroup ((MulAction.toPermHom Y Ω).range)) [Q.Normal]
    [IsElementaryAbelian 2 Q]
    (hreg : RegularOnEntire (MulAction.toPermHom Y Ω).range Q)
    (A : Subgroup Y) (hodd : Odd (Nat.card A)) (α β : Ω) (hne : α ≠ β)
    (hα : ∀ a ∈ A, a • α = α) (hβ : ∀ a ∈ A, a • β = β) :
    Nat.card Ω = 4 ∧ ∀ a ∈ A, ∀ γ : Ω, a • γ = γ := by
  have hfour := binary_regular_normal_image_degree_four hno hdegree Q hreg
  exact ⟨hfour, four_point_odd_pair_subgroup_fixes_every_point hfour A hodd α β hne hα hβ⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
