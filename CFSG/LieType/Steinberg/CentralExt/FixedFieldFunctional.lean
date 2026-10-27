module

public import Mathlib.LinearAlgebra.Dual.Lemmas

public noncomputable section

namespace CFSG.LieType.Steinberg.CentralExt

variable {K : Type*} [Field K] (σ : K →+* K)

@[expose] def fixedPhi :
    K →ₗ[RingHom.eqLocusField σ (RingHom.id K)] RingHom.eqLocusField σ (RingHom.id K) :=
  (Module.Projective.exists_dual_eq_one (RingHom.eqLocusField σ (RingHom.id K))
    (one_ne_zero (α := K))).choose

theorem fixedPhi_one : fixedPhi σ 1 = 1 :=
  (Module.Projective.exists_dual_eq_one (RingHom.eqLocusField σ (RingHom.id K))
    (one_ne_zero (α := K))).choose_spec

theorem fixedPhi_coe (a : RingHom.eqLocusField σ (RingHom.id K)) : fixedPhi σ (a : K) = a := by
  have h : (a : K) = a • (1 : K) := by rw [Algebra.smul_def, mul_one]; rfl
  rw [h, map_smul, fixedPhi_one, smul_eq_mul, mul_one]

theorem fixedPhi_surjective : Function.Surjective (fixedPhi σ) := fun a => ⟨a, fixedPhi_coe σ a⟩

theorem fixedPhi_mul (a : RingHom.eqLocusField σ (RingHom.id K)) (c : K) :
    fixedPhi σ ((a : K) * c) = a * fixedPhi σ c := by
  have h : (a : K) * c = a • c := by rw [Algebra.smul_def]; rfl
  rw [h, map_smul, smul_eq_mul]

end CFSG.LieType.Steinberg.CentralExt
