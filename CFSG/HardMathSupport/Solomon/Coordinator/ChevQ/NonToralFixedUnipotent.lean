module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCoreNorm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false


theorem normalizesRGroup_of_fixed_unipotent {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g : ModGL τ (AlgebraicClosure K)} (hg : g ∈ adjointGroup τ (AlgebraicClosure K))
    {E₀ P : Subgroup (adjointGroup τ K)} {z : adjointGroup τ K} (hz3 : z ^ 3 = 1)
    (hE : E₀ ≤ P ⊔ Subgroup.zpowers z) (hPz : ∀ p ∈ P, Commute z p)
    {z' ν : ModGL τ (AlgebraicClosure K)}
    (hz' : g * z' * g⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL τ K))
    (hν : Units.map (entrywiseHom Fr) g = g * ν)
    {u₁ : ModGL τ (AlgebraicClosure K)} (hu₁G : u₁ ∈ adjointGroup τ (AlgebraicClosure K))
    (hu₁ : u₁ ≠ 1) (hu₁r : u₁ ^ ringChar K = 1)
    (hF : ν * Units.map (entrywiseHom Fr) u₁ * ν⁻¹ = u₁) (hcz : Commute u₁ z')
    (hP : ∀ p ∈ P, Commute u₁
      (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (p : ModGL τ K) * g)) :
    NormalizesRGroup (ringChar K) E₀ := by
  classical
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  have hℓ : ringChar K ≠ 3 := by
    intro h
    apply hK3
    rw [hcard, h]
    exact dvd_pow_self 3 (by omega)
  have hconj : ∀ n : ℕ, z' ^ n * u₁ * (z' ^ n)⁻¹ = u₁ := fun n => by
    rw [(hcz.pow_right n).symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : z' * u₁ * z'⁻¹ = u₁ := by simpa using hconj 1
  have hnt : u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹) ≠ 1 := by
    rw [h1, hconj 2, ← pow_three']
    intro h3
    refine hu₁ ?_
    have hdvd3 : orderOf u₁ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hdvdr : orderOf u₁ ∣ ringChar K := orderOf_dvd_of_pow_eq_one hu₁r
    have hcop : Nat.Coprime 3 (ringChar K) :=
      (Nat.coprime_primes Nat.prime_three (Fact.out : (ringChar K).Prime)).2 hℓ.symm
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvdr)
  obtain ⟨u, hu1, hur, hcu⟩ := exists_rational_centralizing_of_frame_orbit hτ Fr hFr g hg E₀ P z
    hz3 hE hPz z' ν hz' hν u₁ 0 hu₁G hu₁r (by simpa using hF) (by rw [h1]) hnt hP
  exact SeitzExcOpenRest4.normalizesRGroup_of_commute hu1 hur hcu

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

end
