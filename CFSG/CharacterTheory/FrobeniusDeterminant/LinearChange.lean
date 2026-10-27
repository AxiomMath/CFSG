module

public import CFSG.CharacterTheory.FrobeniusDeterminant.Defs
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG

namespace FrobeniusDeterminant.LinearChange

open scoped BigOperators
open MvPolynomial

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

@[expose] noncomputable def linearVar (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (k : κ) :
    MvPolynomial ι ℂ :=
  ∑ i, (L (Pi.single i 1)) k • X i

theorem linearVar_isHomogeneous
    (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (k : κ) :
    (linearVar L k).IsHomogeneous 1 := by
  rw [linearVar]
  apply IsHomogeneous.sum
  intro i hi
  simpa only [smul_eq_C_mul] using
    (isHomogeneous_C (σ := ι) ((L (Pi.single i 1)) k)).mul
    (isHomogeneous_X ℂ i)

@[expose] noncomputable def linearAlgHom (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) :
    MvPolynomial κ ℂ →ₐ[ℂ] MvPolynomial ι ℂ :=
  MvPolynomial.aeval (linearVar L)

@[simp] theorem linearAlgHom_X (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (k : κ) :
    linearAlgHom L (X k) = linearVar L k := by
  simp [linearAlgHom]

theorem aeval_linearVar {A : Type*} [CommRing A] [Algebra ℂ A]
    (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (x : ι → A) (k : κ) :
    MvPolynomial.aeval x (linearVar L k) =
      ∑ i, (L (Pi.single i 1)) k • x i := by
  simp [linearVar]

theorem linearVar_eval (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ))
    (x : ι → ℂ) (k : κ) :
    MvPolynomial.eval x (linearVar L k) = L x k := by
  change MvPolynomial.aeval x (linearVar L k) = L x k
  rw [aeval_linearVar]
  calc
    (∑ i, (L (Pi.single i 1)) k • x i) =
        L (∑ i, x i • Pi.single i 1) k := by
          simp [map_sum, mul_comm]
    _ = L x k := by
      exact congrArg (fun y : ι → ℂ => L y k) (pi_eq_sum_univ' x).symm

private theorem coeff_mul_coeff_symm
    (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (k k' : κ) :
    (∑ i, (L (Pi.single i 1)) k * (L.symm (Pi.single k' 1)) i) =
      if k = k' then 1 else 0 := by
  have h := congrFun (L.apply_symm_apply (Pi.single k' 1)) k
  rw [pi_eq_sum_univ' (L.symm (Pi.single k' 1))] at h
  rw [Pi.single_apply] at h
  simpa [map_sum, mul_comm] using h

theorem linearAlgHom_symm_comp
    (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) :
    (linearAlgHom L.symm).comp (linearAlgHom L) = AlgHom.id ℂ (MvPolynomial κ ℂ) := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [AlgHom.comp_apply, linearAlgHom_X]
  change MvPolynomial.aeval (linearVar L.symm) (linearVar L k) = _
  rw [aeval_linearVar]
  simp only [linearVar, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_smul]
  simp only [AlgHom.id_apply]
  calc
    (∑ k' : κ, ∑ i : ι,
        (L (Pi.single i 1) k * L.symm (Pi.single k' 1) i) • X k') =
        ∑ k' : κ, (∑ i : ι,
          L (Pi.single i 1) k * L.symm (Pi.single k' 1) i) • X k' := by
            apply Finset.sum_congr rfl
            intro k' hk'
            rw [Finset.sum_smul]
    _ = X k := by simp [coeff_mul_coeff_symm]

@[expose] noncomputable def linearAlgEquiv (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) :
    MvPolynomial κ ℂ ≃ₐ[ℂ] MvPolynomial ι ℂ :=
  AlgEquiv.ofAlgHom (linearAlgHom L) (linearAlgHom L.symm)
    (by simpa only [LinearEquiv.symm_symm] using linearAlgHom_symm_comp L.symm)
    (linearAlgHom_symm_comp L)

@[simp] theorem linearAlgEquiv_X (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (k : κ) :
    linearAlgEquiv L (X k) = linearVar L k := by
  exact linearAlgHom_X L k

@[simp] theorem linearAlgEquiv_symm_X (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (i : ι) :
    (linearAlgEquiv L).symm (X i) = linearVar L.symm i := by
  exact linearAlgHom_X L.symm i

theorem aeval_linearAlgEquiv (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ))
    (x : ι → ℂ) (p : MvPolynomial κ ℂ) :
    MvPolynomial.aeval x (linearAlgEquiv L p) =
      MvPolynomial.aeval (L x) p := by
  change ((MvPolynomial.aeval x).comp (linearAlgEquiv L).toAlgHom) p =
    MvPolynomial.aeval (L x) p
  congr 1
  apply MvPolynomial.algHom_ext
  intro k
  simp [linearVar_eval]

theorem irreducible_linearAlgEquiv_iff
    (L : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (p : MvPolynomial κ ℂ) :
    Irreducible (linearAlgEquiv L p) ↔ Irreducible p :=
  MulEquiv.irreducible_iff (linearAlgEquiv L)

end FrobeniusDeterminant.LinearChange

end CFSG
