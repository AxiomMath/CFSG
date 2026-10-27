module

public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizerSupport

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open Matrix CFSG.Wreathed.CentralSL2Abelianization CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.Wreathed.OddFieldTorus CFSG.Semidihedral.ProjectiveSL2Cover

variable {F : Type} [Field F]

theorem weyl_coe :
    ((weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] :=
  rfl

theorem weyl_eq_J₀ : weyl F = J₀ F := rfl

theorem weyl_apply_00 : ((weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
    0 := by simp [weyl]

theorem weyl_apply_01 : ((weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
    -1 := by simp [weyl]

theorem weyl_apply_10 : ((weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
    1 := by simp [weyl]

theorem weyl_apply_11 : ((weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
    0 := by simp [weyl]

theorem SL_coe_inv (A : SpecialLinearGroup (Fin 2) F) :
    ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      adjugate (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem mul_apply_two (A B : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mul_weyl :
    (weyl F : Matrix (Fin 2) (Fin 2) F) * (weyl F : Matrix (Fin 2) (Fin 2) F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply_two, weyl_apply_00, weyl_apply_01, weyl_apply_10, weyl_apply_11]

theorem minusIdentity_coe :
    ((minusIdentity F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  rw [minusIdentity_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mul_weyl_of_conj {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) :
    (X : Matrix (Fin 2) (Fin 2) F) * (weyl F : Matrix (Fin 2) (Fin 2) F) =
      -((weyl F : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F)) := by
  have h : ((X * weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((minusIdentity F * weyl F * X : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) := by
    rw [mul_inv_eq_iff_eq_mul.mp hX]
  rw [SL_coe_mul, SL_coe_mul, SL_coe_mul, minusIdentity_coe] at h
  rw [h, neg_one_mul, neg_mul]

theorem entries_of_conj {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) :
    (X : Matrix (Fin 2) (Fin 2) F) 1 1 = -(X : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      (X : Matrix (Fin 2) (Fin 2) F) 1 0 = (X : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  have h := mul_weyl_of_conj hX
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [mul_apply_two, Matrix.neg_apply, weyl_apply_00, weyl_apply_01, weyl_apply_10,
    weyl_apply_11] at h00 h01
  exact ⟨by linear_combination -h01, by linear_combination -h00⟩

theorem sq_add_sq_of_conj {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) :
    (X : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 + (X : Matrix (Fin 2) (Fin 2) F) 0 1 ^ 2 = -1 := by
  obtain ⟨h1, h2⟩ := entries_of_conj hX
  have hdet := X.2
  rw [Matrix.det_fin_two, h1, h2] at hdet
  linear_combination -hdet

theorem mul_self_of_conj {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) :
    (X : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) = -1 := by
  obtain ⟨h1, h2⟩ := entries_of_conj hX
  have hs := sq_add_sq_of_conj hX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply_two]
  · linear_combination hs + (X : Matrix (Fin 2) (Fin 2) F) 0 1 * h2
  · linear_combination (X : Matrix (Fin 2) (Fin 2) F) 0 1 * h1
  · linear_combination (X : Matrix (Fin 2) (Fin 2) F) 1 0 * h1
  · linear_combination hs + (X : Matrix (Fin 2) (Fin 2) F) 0 1 * h2 +
      ((X : Matrix (Fin 2) (Fin 2) F) 1 1 - (X : Matrix (Fin 2) (Fin 2) F) 0 0) * h1

theorem conj_eq_inv_of_mem_torus {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) {Z : SpecialLinearGroup (Fin 2) F}
    (hZ : Z ∈ torus F) : X * Z * X⁻¹ = Z⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  obtain ⟨h1, h2⟩ := entries_of_conj hX
  obtain ⟨k1, k2⟩ := (mem_torus_coord_iff Z).mp hZ
  apply SL_ext
  rw [SL_coe_mul, SL_coe_mul, SL_coe_inv, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply_two, h1, h2, k1, k2] <;> ring

theorem fieldSL_eq_fieldAction (τ : F ≃+* F) (Z : SpecialLinearGroup (Fin 2) F) :
    fieldSL F τ Z = CFSG.Wreathed.OddFieldTorus.fieldAction F τ Z :=
  rfl

theorem fieldSL_mem_torus (τ : F ≃+* F) {Z : SpecialLinearGroup (Fin 2) F} (hZ : Z ∈ torus F) :
    fieldSL F τ Z ∈ torus F := by
  rw [fieldSL_eq_fieldAction]
  exact fieldAction_mem_torus τ hZ

@[expose] def rMat (X : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  (weyl F : Matrix (Fin 2) (Fin 2) F) + (X : Matrix (Fin 2) (Fin 2) F)

theorem det_rMat {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) : (rMat X).det = 2 := by
  obtain ⟨h1, h2⟩ := entries_of_conj hX
  have hs := sq_add_sq_of_conj hX
  rw [rMat, Matrix.det_fin_two]
  simp [weyl_coe, h1, h2]
  linear_combination -hs

@[expose] noncomputable def rGL (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero (rMat X) (by rw [det_rMat hX]; exact h2)

theorem rGL_coe (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) :
    ((rGL X h2 hX : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = rMat X :=
  rfl

theorem weyl_mul_rGL (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) :
    SpecialLinearGroup.toGL (weyl F) * rGL X h2 hX = rGL X h2 hX * SpecialLinearGroup.toGL X := by
  apply Units.ext
  change (weyl F : Matrix (Fin 2) (Fin 2) F) * rMat X = rMat X * (X : Matrix (Fin 2) (Fin 2) F)
  rw [rMat, mul_add, add_mul, weyl_mul_weyl, mul_self_of_conj hX, add_comm]

@[expose] noncomputable def kappa (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) :
    MulAut (SpecialLinearGroup (Fin 2) F) :=
  matrixConjugation F (rGL X h2 hX)

theorem kappa_toGL (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) (Z : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL (kappa X h2 hX Z) =
      rGL X h2 hX * SpecialLinearGroup.toGL Z * (rGL X h2 hX)⁻¹ :=
  matrixConjugation_toGL F _ Z

theorem weyl_mul_kappa (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) (Z : SpecialLinearGroup (Fin 2) F) :
    weyl F * kappa X h2 hX Z * (weyl F)⁻¹ = kappa X h2 hX (X * Z * X⁻¹) := by
  apply SpecialLinearGroup.toGL_injective
  simp only [map_mul, map_inv, kappa_toGL]
  have h := weyl_mul_rGL X h2 hX
  calc SpecialLinearGroup.toGL (weyl F) * (rGL X h2 hX * SpecialLinearGroup.toGL Z *
        (rGL X h2 hX)⁻¹) * (SpecialLinearGroup.toGL (weyl F))⁻¹ =
      (SpecialLinearGroup.toGL (weyl F) * rGL X h2 hX) * SpecialLinearGroup.toGL Z *
        (SpecialLinearGroup.toGL (weyl F) * rGL X h2 hX)⁻¹ := by group
    _ = (rGL X h2 hX * SpecialLinearGroup.toGL X) * SpecialLinearGroup.toGL Z *
        (rGL X h2 hX * SpecialLinearGroup.toGL X)⁻¹ := by rw [h]
    _ = _ := by group

theorem weyl_conj_kappa_of_mem_torus (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) {Z : SpecialLinearGroup (Fin 2) F}
    (hZ : Z ∈ torus F) : weyl F * kappa X h2 hX Z * (weyl F)⁻¹ = (kappa X h2 hX Z)⁻¹ := by
  rw [weyl_mul_kappa, conj_eq_inv_of_mem_torus hX hZ, map_inv]

theorem map_rGL (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) (τ : F ≃+* F) :
    ((GeneralLinearGroup.map τ.toRingHom (rGL X h2 hX) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
      (weyl F : Matrix (Fin 2) (Fin 2) F) +
        ((fieldSL F τ X : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  change τ (rMat X i j) = _
  rw [rMat, Matrix.add_apply, map_add, Matrix.add_apply]
  congr 1
  rw [weyl_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem mul_fieldSL_kappa (X : SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) (τ : F ≃+* F)
    {w : SpecialLinearGroup (Fin 2) F} (hw : w ∈ torus F) (hwX : w * fieldSL F τ X * w⁻¹ = X)
    {Z : SpecialLinearGroup (Fin 2) F} (hZ : Z ∈ torus F) :
    w * fieldSL F τ (kappa X h2 hX Z) * w⁻¹ = kappa X h2 hX (fieldSL F τ Z) := by
  have hwJ : w * weyl F = weyl F * w := Subgroup.mem_centralizer_singleton_iff.mp hw
  have hwX' : w * fieldSL F τ X = X * w := mul_inv_eq_iff_eq_mul.mp hwX
  have hR : SpecialLinearGroup.toGL w * GeneralLinearGroup.map τ.toRingHom (rGL X h2 hX) =
      rGL X h2 hX * SpecialLinearGroup.toGL w := by
    apply Units.ext
    have h1 : ((w * weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((weyl F * w : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by rw [hwJ]
    have h2' : ((w * fieldSL F τ X : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((X * w : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by rw [hwX']
    rw [SL_coe_mul, SL_coe_mul] at h1 h2'
    change (w : Matrix (Fin 2) (Fin 2) F) *
        ((GeneralLinearGroup.map τ.toRingHom (rGL X h2 hX) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = rMat X * (w : Matrix (Fin 2) (Fin 2) F)
    rw [map_rGL, rMat, mul_add, add_mul, h1, h2']
  have hτZ : fieldSL F τ Z ∈ torus F := fieldSL_mem_torus τ hZ
  have hc : w * fieldSL F τ Z = fieldSL F τ Z * w := torus_comm hw hτZ
  apply SpecialLinearGroup.toGL_injective
  have hc' : SpecialLinearGroup.toGL w * SpecialLinearGroup.toGL (fieldSL F τ Z) =
      SpecialLinearGroup.toGL (fieldSL F τ Z) * SpecialLinearGroup.toGL w := by
    rw [← map_mul, hc, map_mul]
  simp only [map_mul, map_inv, kappa_toGL, fieldSL_toGL] at hc' ⊢
  calc SpecialLinearGroup.toGL w * (GeneralLinearGroup.map τ.toRingHom (rGL X h2 hX) *
        GeneralLinearGroup.map τ.toRingHom (SpecialLinearGroup.toGL Z) *
        (GeneralLinearGroup.map τ.toRingHom (rGL X h2 hX))⁻¹) *
        (SpecialLinearGroup.toGL w)⁻¹ =
      (SpecialLinearGroup.toGL w * GeneralLinearGroup.map τ.toRingHom (rGL X h2 hX)) *
        GeneralLinearGroup.map τ.toRingHom (SpecialLinearGroup.toGL Z) *
        (SpecialLinearGroup.toGL w * GeneralLinearGroup.map τ.toRingHom (rGL X h2 hX))⁻¹ := by
        group
    _ = (rGL X h2 hX * SpecialLinearGroup.toGL w) *
        GeneralLinearGroup.map τ.toRingHom (SpecialLinearGroup.toGL Z) *
        (rGL X h2 hX * SpecialLinearGroup.toGL w)⁻¹ := by rw [hR]
    _ = rGL X h2 hX * (SpecialLinearGroup.toGL w *
        GeneralLinearGroup.map τ.toRingHom (SpecialLinearGroup.toGL Z)) *
        (SpecialLinearGroup.toGL w)⁻¹ * (rGL X h2 hX)⁻¹ := by group
    _ = rGL X h2 hX * (GeneralLinearGroup.map τ.toRingHom (SpecialLinearGroup.toGL Z) *
        SpecialLinearGroup.toGL w) * (SpecialLinearGroup.toGL w)⁻¹ * (rGL X h2 hX)⁻¹ := by
        rw [hc']
    _ = _ := by group

end CFSG.Wreathed.OriginalAllPrime.IVFacts
