module

public import CFSG.LieType.SpecialLinear.BorelTwist.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

variable (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
variable (A : GL (Fin (m + 1)) F)

omit [Finite F] [CharP F 2] in
theorem slFieldAut_matrix (σ : F ≃+* F)
    (g : SpecialLinearGroup (Fin (m + 1)) F) :
    ((CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ g :
        SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ.toRingHom := by
  ext i j
  change CatalogueBHigherLinearField.slFieldEquiv (Fin (m + 1)) σ g i j = _
  rw [CatalogueBHigherLinearField.slFieldEquiv_entry]
  rfl

theorem stdAut_zero_mem_U (hA : IsUpperGL A) (σ : F ≃+* F)
    {u : SpecialLinearGroup (Fin (m + 1)) F} (hu : u ∈ (curtisDatum m F 2).U) :
    CFSG.QuasithinUnique.K1.stdAut A σ 0 u ∈ (curtisDatum m F 2).U := by
  have hAtri : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperTriangular := hA
  have hAinv : ((A⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperTriangular := by
    simpa [Matrix.coe_units_inv] using Matrix.blockTriangular_inv_of_blockTriangular hAtri
  have hu' := (mem_curtisDatum_U_iff (m := m) (F := F) (p := 2)).mp hu
  have hu_mat : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperUnitriangular :=
    (Matrix.isUpperUnitriangular_def _).mpr ⟨hu'.2, hu'.1⟩
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ.toRingHom with hY
  have hYtri : Y.IsUpperUnitriangular := by
    rw [hY]
    exact hu_mat.map σ.toRingHom
  rw [mem_curtisDatum_U_iff]
  refine ⟨?_, ?_⟩
  · intro i
    rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    change ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Y *
      ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) i i = 1
    rw [Matrix.mul_apply_diag_of_isUpperTriangular
      (show (((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Y)).IsUpperTriangular from
        hAtri.mul hYtri.isUpperTriangular) hAinv i]
    rw [Matrix.mul_apply_diag_of_isUpperTriangular hAtri hYtri.isUpperTriangular i,
      hYtri.apply_diag i, mul_one]
    rw [mul_comm (A i i)]
    simpa [Matrix.coe_units_inv] using
      Matrix.inv_apply_diag_mul_of_isUpperTriangular hAtri i
  · intro i j hji
    rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    change ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Y *
      ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) i j = 0
    exact (hAtri.mul hYtri.isUpperTriangular).mul hAinv hji

theorem stdAut_zero_torus (hA : IsUpperGL A) (σ : F ≃+* F)
    {h : SpecialLinearGroup (Fin (m + 1)) F} (hh : h ∈ (curtisDatum m F 2).H) :
    (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h)⁻¹ *
        CFSG.QuasithinUnique.K1.stdAut A σ 0 h ∈ (curtisDatum m F 2).U := by
  have hAtri : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperTriangular := hA
  have hAinv : ((A⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsUpperTriangular := by
    simpa [Matrix.coe_units_inv] using Matrix.blockTriangular_inv_of_blockTriangular hAtri
  have hh' := (mem_curtisDatum_H_iff (m := m) (F := F) (p := 2)).mp hh
  have hhinv : h⁻¹ ∈ (curtisDatum m F 2).H := inv_mem hh
  have hhinv' := (mem_curtisDatum_H_iff (m := m) (F := F) (p := 2)).mp hhinv
  set D : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ.toRingHom with hD
  set E : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    ((h⁻¹ : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ.toRingHom with hE
  have hDtri : D.IsUpperTriangular := by
    intro i j hij
    rw [hD, Matrix.map_apply, hh' i j (ne_of_gt hij), map_zero]
  have hEtri : E.IsUpperTriangular := by
    intro i j hij
    rw [hE, Matrix.map_apply, hhinv' i j (ne_of_gt hij), map_zero]
  have hcoed : ((CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h :
      SpecialLinearGroup (Fin (m + 1)) F) : Matrix _ _ F) = D := by
    rw [hD]
    exact slFieldAut_matrix m F σ h
  have hcoed' : ((CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h⁻¹ :
      SpecialLinearGroup (Fin (m + 1)) F) : Matrix _ _ F) = E := by
    rw [hE]
    exact slFieldAut_matrix m F σ h⁻¹
  have hDE : D * E = 1 := by
    rw [← hcoed, ← hcoed', ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel,
      map_one, Matrix.SpecialLinearGroup.coe_one]
  have hDinvE : D⁻¹ = E := Matrix.inv_eq_right_inv hDE
  rw [mem_curtisDatum_U_iff]
  have hfinv : (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h)⁻¹ =
      CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h⁻¹ := by
    rw [← map_inv]
  have hmat : (((CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h)⁻¹ *
      CFSG.QuasithinUnique.K1.stdAut A σ 0 h :
      SpecialLinearGroup (Fin (m + 1)) F) : Matrix _ _ F) =
      E * (A : Matrix _ _ F) * D * ((A⁻¹ : GL (Fin (m + 1)) F) :
        Matrix _ _ F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, CFSG.QuasithinUnique.K1.coe_stdAut_zero,
      hfinv, hcoed']
    change E * ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * D *
      ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) =
      E * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * D *
        ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    noncomm_ring
  rw [hmat]
  refine ⟨?_, ?_⟩
  · intro i
    rw [Matrix.mul_apply_diag_of_isUpperTriangular
      (show (E * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * D).IsUpperTriangular from
        (hEtri.mul hAtri).mul hDtri) hAinv i]
    rw [Matrix.mul_apply_diag_of_isUpperTriangular
      (show (E * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).IsUpperTriangular from
        hEtri.mul hAtri) hDtri i]
    rw [Matrix.mul_apply_diag_of_isUpperTriangular hEtri hAtri i]
    have hED : E * D = 1 := mul_eq_one_comm.mpr hDE
    have hEDii : E i i * D i i = 1 := by
      rw [← Matrix.mul_apply_diag_of_isUpperTriangular hEtri hDtri i]
      simpa using congrFun (congrFun hED i) i
    have hAAinv : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i *
        ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1 := by
      have h := Matrix.inv_apply_diag_mul_of_isUpperTriangular hAtri i
      rw [Matrix.coe_units_inv]
      rwa [mul_comm] at h
    calc E i i * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i * D i i *
          ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i
        = (E i i * D i i) * ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i *
            ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) := by
          ring
      _ = 1 := by rw [hEDii, hAAinv, one_mul]
  · intro i j hji
    exact ((hEtri.mul hAtri).mul hDtri).mul hAinv hji

theorem slFieldAut_mem_H (σ : F ≃+* F) {h : SpecialLinearGroup (Fin (m + 1)) F}
    (hh : h ∈ (curtisDatum m F 2).H) :
    CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ h ∈
      (curtisDatum m F 2).H := by
  rw [mem_curtisDatum_H_iff] at hh ⊢
  intro i j hij
  rw [slFieldAut_matrix]
  simp [Matrix.map_apply, hh i j hij]

omit [Finite F] [CharP F 2] in
theorem slFieldAut_hdiag (σ : F ≃+* F) (s : Fin m) (u : Fˣ) :
    CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ (hdiag m F s u) =
      hdiag m F s (Units.map σ.toMonoidHom u) := by
  apply Subtype.ext
  rw [slFieldAut_matrix, hdiag_matrix, hdiag_matrix]
  ext i j
  simp only [Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

end CFSG.LieType.SpecialLinear
