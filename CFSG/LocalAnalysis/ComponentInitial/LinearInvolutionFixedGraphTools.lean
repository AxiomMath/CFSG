module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module CFSG.ComponentClassification.CatalogueBAlternatingIsometry

variable {n : ℕ} {K : Type*} [Field K]

theorem conjAut_dualAut_proj_of_transpose_mul_mul (A : GL (Fin n) K)
    (g : SpecialLinearGroup (Fin n) K)
    (hg : (g : Matrix (Fin n) (Fin n) K)ᵀ * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    (conjAut n K A * dualAut n K) (proj n K g) = proj n K g := by
  rw [MulAut.mul_apply]
  refine (congrArg (conjAut n K A) (dualAut_proj _)).trans ((conjAut_proj A _).trans ?_)
  congr 1
  apply Subtype.ext
  refine (coe_slConjugation A _).trans ?_
  set M := (g : Matrix (Fin n) (Fin n) K) with hM
  set R := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hR
  change (A : Matrix (Fin n) (Fin n) K) * (adjugate M)ᵀ * R = M
  have hN : (adjugate M)ᵀ * Mᵀ = 1 := by
    rw [← transpose_mul, mul_adjugate, show M.det = 1 from g.2, one_smul, transpose_one]
  have hRM : R * M = (adjugate M)ᵀ * R := by
    calc R * M = ((adjugate M)ᵀ * Mᵀ) * (R * M) := by rw [hN, Matrix.one_mul]
      _ = (adjugate M)ᵀ * (Mᵀ * R * M) := by simp only [Matrix.mul_assoc]
      _ = (adjugate M)ᵀ * R := by rw [hg]
  have hAR : (A : Matrix (Fin n) (Fin n) K) * R = 1 := by
    rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (A : Matrix (Fin n) (Fin n) K) * (adjugate M)ᵀ * R =
        (A : Matrix (Fin n) (Fin n) K) * (R * M) := by rw [Matrix.mul_assoc, hRM]
    _ = M := by rw [← Matrix.mul_assoc, hAR, Matrix.one_mul]

theorem exists_fixed_perfect_even_conjAut_dualAut_of_basis {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : GL (Fin n) K) (b : Basis ι K (Fin n → K)) {H : Type*} [Group H]
    [Group.IsPerfect H] (Y : H →* GL ι K)
    (hY : ∀ h, ((Y h : GL ι K) : Matrix ι ι K)ᵀ *
      LinearMap.BilinForm.toMatrix b
        (toBilin' ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        (Y h : Matrix ι ι K) =
      LinearMap.BilinForm.toMatrix b
        (toBilin' ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (x : H) (hx4 : x ^ 4 = 1) (hxs : ∀ c : K, (Y x : Matrix ι ι K) ≠ scalar ι c) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, (conjAut n K A * dualAut n K) s = s := by
  set R := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hR
  set B := toBilin' R with hB
  let ρ : H →* GL (Fin n) K :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm.toMonoidHom.comp
        ((basisMatrixEquiv b).symm.toMonoidHom.comp Y))
  have hρ : ∀ h, ((ρ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      LinearMap.toMatrix' ((basisMatrixEquiv b).symm (Y h)).toLinearMap := fun h => rfl
  have hiso : ∀ h, (basisMatrixEquiv b).symm (Y h) ∈ isometryGroup B := fun h => by
    rw [isometry_iff_matrix b, MulEquiv.apply_symm_apply]
    exact hY h
  have hstd : ∀ h, ((ρ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ * R *
      (ρ h : Matrix (Fin n) (Fin n) K) = R := fun h => by
    have h1 := (isometry_iff_matrix (Pi.basisFun K (Fin n)) B _).1 (hiso h)
    rw [basisMatrixEquiv_val, LinearMap.toMatrix_eq_toMatrix', hB,
      LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h1
    rw [hρ]
    exact h1
  refine exists_fixed_perfect_even_of_hom ρ _
    (fun g hg => conjAut_dualAut_proj_of_transpose_mul_mul A ⟨_, hg⟩ (hstd g)) x hx4 ?_
  intro c hc
  apply hxs c
  have hg : ((basisMatrixEquiv b).symm (Y x)).toLinearMap = c • LinearMap.id := by
    apply LinearMap.toMatrix'.injective
    rw [← hρ x, hc, map_smul, LinearMap.toMatrix'_id, scalar_apply, smul_one_eq_diagonal]
  conv_lhs => rw [← MulEquiv.apply_symm_apply (basisMatrixEquiv b) (Y x)]
  rw [basisMatrixEquiv_val, hg, map_smul, LinearMap.toMatrix_id, scalar_apply,
    smul_one_eq_diagonal]

theorem transpose_eq_or_eq_neg_of_sq_conjAut_dualAut [Finite K] (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hα : (conjAut n K A * dualAut n K) ^ 2 = 1) :
    (A : Matrix (Fin n) (Fin n) K)ᵀ = A ∨ (A : Matrix (Fin n) (Fin n) K)ᵀ = -A := by
  have hδδ : dualAut n K * dualAut n K = 1 :=
    (standard_automorphism_transport (n := n) (K := K)).2.2.2.1
  have hsq : conjAut n K (A * GeneralLinearGroup.inverseTranspose A) * fieldAut n K 1 = 1 := by
    calc conjAut n K (A * GeneralLinearGroup.inverseTranspose A) * fieldAut n K 1
        = conjAut n K A * (dualAut n K * conjAut n K A) * dualAut n K := by
          rw [map_one (fieldAut n K), mul_one, dualAut_mul_conjAut, map_mul, mul_assoc,
            mul_assoc, hδδ, mul_one]
      _ = (conjAut n K A * dualAut n K) ^ 2 := by rw [sq]; simp only [mul_assoc]
      _ = 1 := hα
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ hsq
  set M := (A : Matrix (Fin n) (Fin n) K) with hM
  have hcM : (c : K) • (1 : Matrix (Fin n) (Fin n) K) =
      M * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
    have h := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hc
    rw [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose] at h
    rw [← h, smul_one_eq_diagonal]
    rfl
  have hA : M = (c : K) • Mᵀ := by
    calc M = M * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ * Mᵀ) := by
          rw [← transpose_mul, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            transpose_one, Matrix.mul_one]
      _ = (c : K) • Mᵀ := by rw [← Matrix.mul_assoc, ← hcM, Matrix.smul_mul, Matrix.one_mul]
  have hAt : Mᵀ = (c : K) • M := by
    conv_lhs => rw [hA]
    rw [transpose_smul, transpose_transpose]
  have hM0 : M ≠ 0 := by
    intro h0
    have hu : IsUnit M.det := Matrix.isUnits_det_units A
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    rw [h0, Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  have hcc : (c : K) * c = 1 := by
    have h2 : ((c : K) * c - 1) • M = 0 := by
      rw [sub_smul, mul_smul, ← hAt, ← hA, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hM0)
  rcases mul_self_eq_one_iff.1 hcc with h1 | h1
  · left
    rw [hAt, h1, one_smul]
  · right
    rw [hAt, h1, neg_one_smul]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
