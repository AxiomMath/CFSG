module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Orbits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Parabolic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F]

@[expose] noncomputable def thetaFun (g : SL3 F) : SL3 F :=
  ⟨(((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ, by
    rw [Matrix.det_transpose]
    exact (g⁻¹).2⟩

theorem coe_thetaFun (g : SL3 F) :
    ((thetaFun g : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ :=
  rfl

theorem thetaFun_mul (g h : SL3 F) : thetaFun (g * h) = thetaFun g * thetaFun h := by
  refine Subtype.ext ?_
  change (((g * h)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)ᵀ =
    (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ * (((h⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ
  rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem thetaFun_thetaFun (g : SL3 F) : thetaFun (thetaFun g) = g := by
  refine Subtype.ext ?_
  change (((thetaFun g)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)ᵀ = (g : Matrix (Fin 3) (Fin 3) F)
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_thetaFun, Matrix.adjugate_transpose,
    Matrix.transpose_transpose, ← Matrix.SpecialLinearGroup.coe_inv, inv_inv]

@[expose] noncomputable def theta : SL3 F ≃* SL3 F where
  toFun := thetaFun
  invFun := thetaFun
  left_inv := thetaFun_thetaFun
  right_inv := thetaFun_thetaFun
  map_mul' := thetaFun_mul

theorem theta_apply (g : SL3 F) : theta g = thetaFun g := rfl

theorem theta_mem_P1_of_mem_P2 {g : SL3 F} (hg : g ∈ P2) : theta g ∈ P1 := by
  have hgi : g⁻¹ ∈ P2 := P2.inv_mem hg
  rw [mem_P2] at hgi
  rw [mem_P1, theta_apply, coe_thetaFun, Matrix.transpose_apply, Matrix.transpose_apply]
  exact hgi

@[expose] noncomputable def kGL : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by simp [Matrix.det_fin_two])

theorem theta_lev (X : GL (Fin 2) F) : theta (lev X) = lev (transposeGL X⁻¹) := by
  refine Subtype.ext ?_
  change (((lev X)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)ᵀ = levMat _
  rw [← map_inv, coe_lev, coe_transposeGL]
  have hdet : ((X⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← isUnit_iff_ne_zero]
    exact Matrix.isUnit_det_of_invertible _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, Matrix.det_transpose]

theorem transposeGL_cGL_inv :
    transposeGL (cGL (F := F))⁻¹ = kGL * (cGL (F := F))⁻¹ * kGL⁻¹ := by
  have hCinv : ((cGL (F := F))⁻¹ : GL (Fin 2) F) =
      GeneralLinearGroup.mkOfDetNeZero !![-1, 1; -1, 0] (by simp [Matrix.det_fin_two]) := by
    rw [inv_eq_iff_mul_eq_one]
    refine Units.ext ?_
    rw [Units.val_mul, coe_cGL, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cMat, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
  rw [eq_mul_inv_iff_mul_eq, hCinv]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kGL, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] noncomputable def dualAut : SL3 F ≃* SL3 F :=
  theta.trans (MulAut.conj (lev (kGL (F := F)))⁻¹)

theorem dualAut_apply (g : SL3 F) :
    dualAut g = (lev (kGL (F := F)))⁻¹ * theta g * lev (kGL (F := F)) := by
  simp [dualAut]

theorem dualAut_lev_cGL : dualAut (lev (cGL (F := F))) = (lev (cGL (F := F)))⁻¹ := by
  rw [dualAut_apply, theta_lev, transposeGL_cGL_inv, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  group

theorem dualAut_mem_P1 {g : SL3 F} (hg : g ∈ P2) : dualAut g ∈ P1 := by
  rw [dualAut_apply]
  have hk := lev_mem_P1 (kGL (F := F))
  exact P1.mul_mem (P1.mul_mem (P1.inv_mem hk) (theta_mem_P1_of_mem_P2 hg)) hk

theorem map_dualAut_A0 :
    (A0 : Subgroup (SL3 F)).map (dualAut (F := F)).toMonoidHom = A0 := by
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (dualAut (lev (cGL (F := F)))) = A0
  rw [dualAut_lev_cGL, Subgroup.zpowers_inv]

theorem map_dualAut_normalizer_A0 :
    (Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F))).map
      (dualAut (F := F)).toMonoidHom =
      Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) := by
  rw [Subgroup.map_equiv_normalizer_eq, map_dualAut_A0]

theorem index_of_le_P2 [Finite F] (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) (h3 : (3 : F) ≠ 0) (hmax : GL2NonsplitMax F)
    {W : Subgroup (SL3 F)} (hWP : W ≤ P2)
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W)
    (hW : ¬ Group.IsSolvable W) :
    W.index = Nat.card F ^ 2 + Nat.card F + 1 ∨
      W.index = Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1) := by
  set W' := W.map (dualAut (F := F)).toMonoidHom
  have hW'P : W' ≤ P1 := by
    rintro _ ⟨g, hg, rfl⟩
    exact dualAut_mem_P1 (hWP hg)
  have hNW' : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W' := by
    rw [← map_dualAut_normalizer_A0]
    exact Subgroup.map_mono hNW
  have hW' : ¬ Group.IsSolvable W' := by
    intro hs
    apply hW
    set e := W.equivMapOfInjective (dualAut (F := F)).toMonoidHom (dualAut (F := F)).injective
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have h := index_of_le_P1 hroot hcube h3 hmax hW'P hNW' hW'
  have hidx : W'.index = W.index := Subgroup.index_map_equiv W (dualAut (F := F))
  rwa [hidx] at h

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
