module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarKernelReduction
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasTwo

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {σ : K ≃+* K}

theorem fixesSingularLines_of_scalar (T : V ≃ₛₗ[σ.toRingHom] V) (a : Kˣ)
    (ha : ∀ v, T v = (a : K) • v) : FixesSingularLines Q T := by
  apply (fixesSingularLines_iff_vectors T).mpr
  exact fun v _ _ => ⟨a, ha v⟩

theorem scalar_kernel_actions [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hS : ∃ S : Submodule K V, finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (T : V ≃ₛₗ[σ.toRingHom] V) (μ : Kˣ)
    (hT : ∀ v, Q (T v) = (μ : K) * σ (Q v)) (hfix : FixesSingularLines Q T) :
    σ = RingEquiv.refl K ∧ ∃ a : Kˣ, (∀ v, T v = (a : K) • v) ∧
      (∀ v, T.symm v = (↑(a⁻¹) : K) • v) ∧ (μ : K) = (a : K) ^ 2 := by
  obtain ⟨S, hS3, hSs⟩ := hS
  obtain ⟨e, heS, he0⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_ne_zero_of_one_le_finrank (T := S) (by omega)
  obtain ⟨P, R, _, _, hPR, _, _⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quadratic_three_hyperbolic_pairs hQ
      ⟨S, hS3, hSs⟩ (hSs e heS) he0
  exact scalar_of_two_pairs hPR T μ hT ((fixesSingularLines_iff_vectors T).mp hfix)

theorem semilinear_singular_point_kernel [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hS : ∃ S : Submodule K V, finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (T : V ≃ₛₗ[σ.toRingHom] V) (μ : Kˣ)
    (hT : ∀ v, Q (T v) = (μ : K) * σ (Q v)) :
    FixesSingularLines Q T ↔
      σ = RingEquiv.refl K ∧ ∃ a : Kˣ, ∀ v, T v = (a : K) • v := by
  constructor
  · intro hfix
    obtain ⟨hσ, a, ha, _, _⟩ := scalar_kernel_actions hQ hS T μ hT hfix
    exact ⟨hσ, a, ha⟩
  · rintro ⟨_, a, ha⟩
    exact fixesSingularLines_of_scalar T a ha

theorem semilinear_singular_vector_kernel [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hS : ∃ S : Submodule K V, finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (T : V ≃ₛₗ[σ.toRingHom] V) (μ : Kˣ)
    (hT : ∀ v, Q (T v) = (μ : K) * σ (Q v)) :
    FixesSingularVectors Q T ↔
      σ = RingEquiv.refl K ∧ ∃ a : Kˣ, ∀ v, T v = (a : K) • v := by
  rw [← fixesSingularLines_iff_vectors T]
  exact semilinear_singular_point_kernel hQ hS T μ hT

theorem scalar_kernel_original_identities [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hS : ∃ S : Submodule K V, finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (T : V ≃ₛₗ[σ.toRingHom] V) (μ : Kˣ)
    (hT : ∀ v, Q (T v) = (μ : K) * σ (Q v)) (hfix : FixesSingularLines Q T) :
    ∃ (hσ : σ = RingEquiv.refl K) (a : Kˣ),
      originalLinearEquiv T hσ = LinearEquiv.smulOfUnit a ∧
      (∀ c : K, σ c = c) ∧ (∀ c : K, ∀ v : V, T (c • v) = c • T v) ∧
      (∀ v, T v = (a : K) • v) ∧ (∀ v, T.symm v = (↑(a⁻¹) : K) • v) ∧
      (μ : K) = (a : K) ^ 2 := by
  obtain ⟨hσ, a, ha, hi, hμ⟩ := scalar_kernel_actions hQ hS T μ hT hfix
  refine ⟨hσ, a, ?_, ?_, ?_, ha, hi, hμ⟩
  · apply LinearEquiv.ext
    intro v
    exact ha v
  · intro c
    simp [hσ]
  · intro c v
    rw [T.map_smulₛₗ]
    simp [hσ]

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel
