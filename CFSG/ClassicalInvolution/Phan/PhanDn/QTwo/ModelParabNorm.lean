module

public import CFSG.ClassicalInvolution.Phan.PhanDn.BaseChange

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP K 2]

theorem normQuad_preserver_eq_id_or_bar {σ : K ≃+* K} (E : QuadExt F K σ)
    (f : K →ₗ[F] K) (hN : ∀ a : K, normQuad E (f a) = normQuad E a) (h1 : f 1 = 1) :
    (∀ a : K, f a = a) ∨ (∀ a : K, f a = σ a) := by
  have hnorm (a : K) : f a * σ (f a) = a * σ a := by
    simpa only [algebraMap_normQuad] using congrArg (algebraMap F K) (hN a)
  have htrace (a : K) : f a + σ (f a) = a + σ a := by
    have h := hnorm (a + 1)
    rw [map_add, h1, map_add, map_one, map_add, map_one] at h
    linear_combination h - hnorm a
  have hroot : (f (bcTheta E) - bcTheta E) * (f (bcTheta E) - σ (bcTheta E)) = 0 := by
    linear_combination f (bcTheta E) * htrace (bcTheta E) - hnorm (bcTheta E)
  have hscalar (a : F) : f (algebraMap F K a) = algebraMap F K a := by
    have h := f.map_smul a (1 : K)
    simpa [Algebra.smul_def, h1] using h
  have hcomb (a b : F) :
      f (algebraMap F K a + algebraMap F K b * bcTheta E) =
        algebraMap F K a + algebraMap F K b * f (bcTheta E) := by
    rw [map_add, hscalar]
    exact congrArg (algebraMap F K a + ·)
      (by simpa [Algebra.smul_def] using f.map_smul b (bcTheta E))
  rcases mul_eq_zero.mp hroot with h | h
  · left
    have ht := sub_eq_zero.mp h
    intro a
    obtain ⟨u, v, hrepr⟩ := exists_eq_algebraMap_add_algebraMap_mul E a
    rw [hrepr, hcomb, ht]
  · right
    have ht := sub_eq_zero.mp h
    intro a
    obtain ⟨u, v, hrepr⟩ := exists_eq_algebraMap_add_algebraMap_mul E a
    rw [hrepr, hcomb, ht, map_add, map_mul, E.fix, E.fix]

theorem normQuad_preserver_eq_mul_or_mul_bar {σ : K ≃+* K} (E : QuadExt F K σ)
    (f : K →ₗ[F] K) (hN : ∀ a : K, normQuad E (f a) = normQuad E a) :
    ∃ u : K, u * σ u = 1 ∧ ((∀ a : K, f a = u * a) ∨ (∀ a : K, f a = u * σ a)) := by
  have hnorm (a : K) : f a * σ (f a) = a * σ a := by
    simpa only [algebraMap_normQuad] using congrArg (algebraMap F K) (hN a)
  have hu : f 1 * σ (f 1) = 1 := by simpa using hnorm 1
  have hu0 : f 1 ≠ 0 := left_ne_zero_of_mul_eq_one hu
  let f' : K →ₗ[F] K :=
    { toFun := fun a => (f 1)⁻¹ * f a
      map_add' := fun a b => by rw [map_add, mul_add]
      map_smul' := fun c a => by
        change (f 1)⁻¹ * f (c • a) = c • ((f 1)⁻¹ * f a)
        rw [f.map_smul]
        simp only [Algebra.smul_def]
        ring }
  have hf' : ∀ a : K, normQuad E (f' a) = normQuad E a := by
    intro a
    apply (algebraMap F K).injective
    rw [algebraMap_normQuad, algebraMap_normQuad]
    change (f 1)⁻¹ * f a * σ ((f 1)⁻¹ * f a) = a * σ a
    calc (f 1)⁻¹ * f a * σ ((f 1)⁻¹ * f a)
        = (f 1 * σ (f 1))⁻¹ * (f a * σ (f a)) := by
          simp only [map_mul, map_inv₀, mul_inv_rev]
          ring
      _ = a * σ a := by rw [hu, inv_one, one_mul, hnorm]
  have hf'1 : f' 1 = 1 := inv_mul_cancel₀ hu0
  refine ⟨f 1, hu, ?_⟩
  rcases normQuad_preserver_eq_id_or_bar E f' hf' hf'1 with h | h
  · left
    intro a
    have ha := congrArg (f 1 * ·) (h a)
    simpa [f', ← mul_assoc, hu0] using ha
  · right
    intro a
    have ha := congrArg (f 1 * ·) (h a)
    simpa [f', ← mul_assoc, hu0] using ha

end CFSG.ClassicalInvolution.PhanDn
