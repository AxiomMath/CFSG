module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
import CFSG.LieType.Ree.SmallReeThreeDerived

public section

namespace CFSG.AGLEmbedding.ReeCenterOver

open Equiv CFSG.AGLEmbedding.ReeModel CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

variable {a : ℕ} {K : Type} [Field K]

theorem g2U₀_eq_smallReeCoord : ReeTag.g2U₀ K = smallReeCoord a K 0 0 1 := by
  have h3 : smallReeRoot 3 = g2Root12 := rfl
  have h5 : smallReeRoot 5 = g2Root23 := rfl
  have hσ0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  have hσ1 : smallReeSigma a (1 : K) = 1 := one_pow _
  show _ = smallReeCoord a K 0 0 1
  rw [smallReeCoord, hσ0, hσ1]
  simp only [zero_pow (by norm_num : 3 ≠ 0), zero_mul, mul_zero, sub_zero, smallReeX_zero,
    one_mul, mul_one]
  rw [smallReeX, smallReeX, h3, h5]
  rfl

variable [CharP K ReeTag.G2.prime] {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)

include hw₀ in
theorem longest_sq_and_commutator :
    canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ *
        canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ = 1 ∧
    ((ReeTag.g2U₀ K) * canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ * (ReeTag.g2U₀ K)⁻¹ *
      (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀)⁻¹) ^ 9 = 1 ∧
    ((ReeTag.g2U₀ K) * canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ * (ReeTag.g2U₀ K)⁻¹ *
      (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀)⁻¹) ^ 3 ≠ 1 := by
  set q0 : srGraph K := ⟨_, srGraph_u0 K⟩
  set qn : srGraph K := ⟨_, srGraph_n K hw₀⟩
  have h1 : srFst K q0 = ReeTag.g2U₀ K := rfl
  have h2 : srSnd K q0 = srSigma0 := rfl
  have h3 : srFst K qn = canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ := rfl
  have h4 : srSnd K qn = srSigmaN := rfl
  have hσn : srSigmaN * srSigmaN = 1 := by decide +kernel
  have hc9 : (srSigma0 * srSigmaN * srSigma0⁻¹ * srSigmaN⁻¹) ^ 9 = 1 := by decide +kernel
  have hc3 : (srSigma0 * srSigmaN * srSigma0⁻¹ * srSigmaN⁻¹) ^ 3 ≠ 1 := by decide +kernel
  have hsq : qn * qn = 1 := srSnd_injective K (by rw [map_mul, h4, hσn, map_one])
  have hsq' := congrArg (srFst K) hsq
  rw [map_mul, h3, map_one] at hsq'
  set c : srGraph K := q0 * qn * q0⁻¹ * qn⁻¹ with hc
  have hcF : srFst K c = ReeTag.g2U₀ K * canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ *
      (ReeTag.g2U₀ K)⁻¹ * (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀)⁻¹ := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, h1, h3]
  have hcS : srSnd K c = srSigma0 * srSigmaN * srSigma0⁻¹ * srSigmaN⁻¹ := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, h2, h4]
  refine ⟨hsq', ?_, ?_⟩
  · have h9 : c ^ 9 = 1 := srSnd_injective K (by rw [map_pow, hcS, hc9, map_one])
    have := congrArg (srFst K) h9
    rwa [map_pow, hcF, map_one] at this
  · intro h
    have h3' : c ^ 3 = 1 := srFst_injective K (by rw [map_pow, hcF, map_one]; exact h)
    exact hc3 (by have := congrArg (srSnd K) h3'; rwa [map_pow, hcS, map_one] at this)

end CFSG.AGLEmbedding.ReeCenterOver
