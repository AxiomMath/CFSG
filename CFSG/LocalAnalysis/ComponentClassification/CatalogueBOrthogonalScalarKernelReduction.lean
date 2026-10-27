module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarKernelGeometry
public import CFSG.ClassicalGroups.Orthogonal.Lines

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {σ : K ≃+* K}

theorem inverse_apply_of_scalar (T : V ≃ₛₗ[σ.toRingHom] V) (a : Kˣ)
    (ha : ∀ v, T v = (a : K) • v) (v : V) :
    T.symm v = (↑(a⁻¹) : K) • v := by
  have hv := ha (T.symm v)
  rw [T.apply_symm_apply] at hv
  have h := congrArg (fun z : V => (↑(a⁻¹) : K) • z) hv
  simpa [smul_smul] using h.symm

theorem scalar_of_two_pairs {P R : HypPair Q} (h : P.Orth R)
    (T : V ≃ₛₗ[σ.toRingHom] V) (μ : Kˣ)
    (hT : ∀ v, Q (T v) = (μ : K) * σ (Q v))
    (hfix : FixesSingularVectors Q T) :
    σ = RingEquiv.refl K ∧ ∃ a : Kˣ, (∀ v, T v = (a : K) • v) ∧
      (∀ v, T.symm v = (↑(a⁻¹) : K) • v) ∧ (μ : K) = (a : K) ^ 2 := by
  have hσ := automorphism_eq_refl_of_two_pairs h T hfix
  obtain ⟨a, ha0, he, hf, -, -⟩ := pair_coefficients h T hfix
  have hμ := multiplier_eq_sq_of_pair T μ hT P he hf
  let u : Kˣ := Units.mk0 a ha0
  let g : V ≃ₗ[K] V := originalLinearEquiv T hσ
  let n : V ≃ₗ[K] V := g.trans (LinearEquiv.smulOfUnit (u⁻¹))
  have hn (v : V) : n v = a⁻¹ • T v := rfl
  have hng : n ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    apply TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
    intro v
    rw [hn, map_smul_eq_sq, hT, hμ]
    simp only [hσ, RingEquiv.refl_apply]
    field_simp
  have hnfix : ∀ v, v ≠ 0 → Q v = 0 → ∃ c : K, n v = c • v := by
    intro v hv hQv
    obtain ⟨c, hc⟩ := hfix v hv hQv
    exact ⟨a⁻¹ * c, by rw [hn, hc, smul_smul]⟩
  obtain ⟨b, hb⟩ := mem_scalars.mp (mem_scalars_of_forall_singular h hng hnfix)
  have hne : n P.e = P.e := by
    rw [hn, he, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have hb1 : b = 1 := by
    apply smul_left_injective K P.e_ne_zero
    change b • P.e = (1 : K) • P.e
    rw [← hb, hne, one_smul]
  have hnid (v : V) : n v = v := by rw [hb, hb1, one_smul]
  have hscalar (v : V) : T v = (u : K) • v := by
    have hv := congrArg (fun z : V => a • z) (hnid v)
    rw [hn, smul_smul, mul_inv_cancel₀ ha0, one_smul] at hv
    exact hv
  exact ⟨hσ, u, hscalar, inverse_apply_of_scalar T u hscalar, hμ⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel
