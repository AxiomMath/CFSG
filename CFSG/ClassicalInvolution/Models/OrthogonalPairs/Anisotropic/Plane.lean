module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Field
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Planes

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {σ : K' ≃+* K'}
  {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem QuadExt.exists_normIso (E : QuadExt K K' σ) (h2 : (2 : K) ≠ 0) {U : Submodule K V}
    (hU : Module.finrank K U = 2) (hs : ¬ HasSingularVector Q U) :
    ∃ φ : K' →ₗ[K] V, (∀ x, φ x ∈ U) ∧ (∀ u ∈ U, ∃ x, φ x = u) ∧
      ∀ x, algebraMap K K' (Q (φ x)) = σ x * x := by
  have : Module.Finite K U := Module.finite_of_finrank_pos (by omega)
  have hU0 : U ≠ ⊥ := by
    intro h
    rw [h] at hU
    simp at hU
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hQu : Q u ≠ 0 := fun h => hs ⟨u, huU, hu0, h⟩
  have hker : (LinearMap.ker ((polarBilin Q u).domRestrict U)) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker ((polarBilin Q u).domRestrict U)
    rw [hbot, finrank_bot, hU] at h1
    have := Submodule.finrank_le (LinearMap.range ((polarBilin Q u).domRestrict U))
    simp only [Module.finrank_self] at this
    omega
  obtain ⟨⟨w, hwU⟩, hwk, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have huw : polar Q u w = 0 := by simpa using hwk
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hQ2 : ∀ s t : K, Q (s • u + t • w) = s ^ 2 * Q u + t ^ 2 * Q w := by
    intro s t
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
      polar_smul_right_eq, huw]
    ring
  have hind : ∀ s t : K, s • u + t • w = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have h1 : polar Q u (s • u + t • w) = 0 := by rw [h, polar_zero_right]
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, huw, polar_self_eq_two_mul]
      at h1
    have hs0 : s = 0 := by
      have : s * (2 * Q u) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' (mul_ne_zero h2 hQu)
    subst hs0
    simp only [zero_smul, zero_add] at h
    exact ⟨rfl, (smul_eq_zero.mp h).resolve_right hw0'⟩
  set δ : K := -Q w / Q u with hδ
  have hnsq : ¬ IsSquare δ := by
    rintro ⟨ε, hε⟩
    apply hs
    refine ⟨ε • u + w, U.add_mem (U.smul_mem ε huU) hwU, ?_, ?_⟩
    · intro h
      have := hind ε 1 (by simpa using h)
      exact one_ne_zero this.2
    · have := hQ2 ε 1
      rw [one_smul] at this
      rw [this, one_pow, one_mul]
      have h3 : Q w = -(Q u * δ) := by rw [hδ]; field_simp
      rw [h3, hε]
      ring
  obtain ⟨r, hr⟩ := E.isSquare δ
  have hr' : r * r = algebraMap K K' δ := hr.symm
  have hrne := not_mem_range_of_sq hnsq hr'
  have hσr := E.sigma_eq_neg hnsq hr'
  let b' := E.basisOneR hrne
  have hb0 : b' 0 = 1 := E.basisOneR_apply hrne 0
  have hb1 : b' 1 = r := E.basisOneR_apply hrne 1
  let φ₀ : K' →ₗ[K] V := b'.constr K ![u, w]
  have hφ₀ : ∀ s t : K, φ₀ (algebraMap K K' s + algebraMap K K' t * r) = s • u + t • w := by
    intro s t
    have : algebraMap K K' s + algebraMap K K' t * r = s • b' 0 + t • b' 1 := by
      rw [hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [this, map_add, map_smul, map_smul]
    simp [φ₀]
  have hdec : ∀ x : K', ∃ s t : K, x = algebraMap K K' s + algebraMap K K' t * r := by
    intro x
    refine ⟨b'.repr x 0, b'.repr x 1, ?_⟩
    conv_lhs => rw [← b'.sum_repr x]
    simp [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def]
  have hnorm : ∀ s t : K, σ (algebraMap K K' s + algebraMap K K' t * r) *
      (algebraMap K K' s + algebraMap K K' t * r) = algebraMap K K' (s ^ 2 - δ * t ^ 2) := by
    intro s t
    rw [map_add, map_mul, E.fix, E.fix, hσr, map_sub, map_mul, map_pow, map_pow]
    have : algebraMap K K' δ = r * r := hr
    rw [this]
    ring
  have hQφ₀ : ∀ x, algebraMap K K' (Q (φ₀ x)) = algebraMap K K' (Q u) * (σ x * x) := by
    intro x
    obtain ⟨s, t, rfl⟩ := hdec x
    rw [hφ₀, hQ2, hnorm, ← map_mul]
    congr 1
    have h3 : Q w = -(Q u * δ) := by rw [hδ]; field_simp
    rw [h3]
    ring
  have hinj : Function.Injective φ₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hQφ₀ x
    rw [hx, QuadraticMap.map_zero, map_zero] at h1
    have h2 : σ x * x = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact absurd (by simpa using h) hQu
      · exact h
    rcases mul_eq_zero.mp h2 with h | h
    · exact (map_eq_zero_iff σ σ.injective).mp h
    · exact h
  have hrange : LinearMap.range φ₀ = U := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨s, t, rfl⟩ := hdec x
      rw [hφ₀]
      exact U.add_mem (U.smul_mem s huU) (U.smul_mem t hwU)
    · rw [LinearMap.finrank_range_of_inj hinj, E.finrank_eq, hU]
  obtain ⟨ε, hε⟩ := E.isUnitary.exists_norm (d := algebraMap K K' (Q u)⁻¹) (E.fix _)
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε
    exact hQu (by simpa using hε.symm)
  refine ⟨φ₀ ∘ₗ LinearMap.mulLeft K ε, fun x => ?_, fun v hv => ?_, fun x => ?_⟩
  · have : φ₀ (ε * x) ∈ LinearMap.range φ₀ := ⟨_, rfl⟩
    rwa [hrange] at this
  · have : v ∈ LinearMap.range φ₀ := by rw [hrange]; exact hv
    obtain ⟨y, rfl⟩ := this
    exact ⟨ε⁻¹ * y, by simp [mul_inv_cancel_left₀ hε0]⟩
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [hQφ₀, map_mul, mul_mul_mul_comm, hε, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hQu,
      map_one, one_mul]

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
