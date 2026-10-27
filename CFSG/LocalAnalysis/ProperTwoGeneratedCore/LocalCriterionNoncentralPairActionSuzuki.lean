module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOvoid

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

open CFSG.BenderSuzuki.MatrixGroups CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.HighRankPair

theorem mem_of_sq_eq_one_of_odd_index {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Odd N.index) {x : X} (hx : x ^ 2 = 1) : x ∈ N := by
  have h2 : (QuotientGroup.mk x : X ⧸ N) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have hdvd : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h)
  · rw [h] at hdvd
    exact absurd (even_iff_two_dvd.mpr hdvd) (Nat.not_even_iff_odd.mpr hN)

theorem suzuki_point_involution_trivial (hSz : SuzukiOuterOdd) {m : ℕ} (hm : 1 ≤ m)
    (θ : MulAut (SuzukiMatrixGroup m)) (hθθ : ∀ x, θ (θ x) = x)
    (τ : {p // p ∈ suzukiOvoidSet m} → {p // p ∈ suzukiOvoidSet m})
    (hτ : letI := suzukiOvoidAction m
      ∀ (x : SuzukiMatrixGroup m) (p : {p // p ∈ suzukiOvoidSet m}), τ (x • p) = θ x • τ p)
    (hττ : ∀ p, τ (τ p) = p) {p₀ p₁ : {p // p ∈ suzukiOvoidSet m}} (hne : p₀ ≠ p₁)
    (h₀ : τ p₀ = p₀) (h₁ : τ p₁ = p₁) : ∀ x, θ x = x := by
  let := suzukiOvoidAction m
  have : (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  obtain ⟨g, rfl⟩ := mem_of_sq_eq_one_of_odd_index (hSz m hm)
    (MulEquiv.ext fun x => by rw [sq, MulAut.mul_apply, hθθ]; rfl)
  have hcard : 2 < Nat.card {p // p ∈ suzukiOvoidSet m} := by
    rw [suzuki_ovoid_card]
    have : 2 ≤ 2 ^ (2 * m + 1) := Nat.le_self_pow (by omega) 2
    nlinarith
  have := suzuki_ovoid_two_transitive m
  have hτg : ∀ p, τ p = g • p := by
    intro p
    have h := eq_self_of_commute_two_pretransitive hcard (fun p => g⁻¹ • τ p)
      (fun x p => by rw [hτ, MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul]) p
    conv_rhs => rw [← h]
    rw [smul_inv_smul]
  obtain ⟨c, hc₀, hc₁⟩ := exists_ne_ne_of_two_lt_card hcard p₀ p₁
  have hg2 : g * g = 1 := by
    by_contra hg
    apply suzuki_ovoid_three_point_free m (by omega) (g * g) hg p₀ p₁ c hne (Ne.symm hc₀)
      (Ne.symm hc₁)
    simp only [mul_smul, ← hτg, hττ, and_self]
  have hg1 : g = 1 := by
    by_contra hg
    obtain ⟨a, -, ha⟩ := suzuki_ovoid_involution_unique_fixed m (by omega) g
      (orderOf_eq_prime (by rw [sq]; exact hg2) hg)
    have hf₀ : g • p₀ = p₀ := by rw [← hτg]; exact h₀
    have hf₁ : g • p₁ = p₁ := by rw [← hτg]; exact h₁
    exact hne ((ha p₀ hf₀).trans (ha p₁ hf₁).symm)
  intro x
  rw [hg1, map_one]
  rfl

end CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction
