module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Involution
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplitProd
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Models.OrthogonalPairs Matrix
open scoped MatrixGroups commutatorElement

variable {K : Type*} [Field K]

theorem reflM_eq_neg_adjugate {v : Matrix (Fin 2) (Fin 2) K} (hv : v.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) K) : reflM v X = -((v.det)⁻¹ • (v * adjugate X * v)) := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_eq_of_fin_two v
  obtain ⟨x, y, z, w, rfl⟩ := exists_eq_of_fin_two X
  simp only [Matrix.det_fin_two_of] at hv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflM, polarDet, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of] <;> field_simp <;>
      ring

theorem reflM_reflM_eq {v w : Matrix (Fin 2) (Fin 2) K} (hv : v.det ≠ 0) (hw : w.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) K) :
    reflM v (reflM w X) =
      (((v.det * w.det)⁻¹ : K) • (v * adjugate w)) * X * (adjugate w * v) := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_eq_of_fin_two v
  obtain ⟨p', q', r', s', rfl⟩ := exists_eq_of_fin_two w
  obtain ⟨x, y, z, t, rfl⟩ := exists_eq_of_fin_two X
  simp only [Matrix.det_fin_two_of] at hv hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflM, polarDet, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of,
      Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem isUnit_det_of_bimul {T : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    {a b : Matrix (Fin 2) (Fin 2) K} (hT : ∀ X, T X = a * X * b) :
    IsUnit a.det ∧ IsUnit b.det := by
  have h1 : a * (T.symm 1) * b = 1 := by rw [← hT]; simp
  have h2 : a.det * (T.symm 1).det * b.det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, h1, Matrix.det_one]
  exact ⟨IsUnit.of_mul_eq_one ((T.symm 1).det * b.det) (by rw [← mul_assoc]; exact h2),
    IsUnit.of_mul_eq_one (a.det * (T.symm 1).det) (by rw [mul_comm]; exact h2)⟩

theorem symm_apply_of_bimul {T : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    {a b : Matrix (Fin 2) (Fin 2) K} (hT : ∀ X, T X = a * X * b) (Y : Matrix (Fin 2) (Fin 2) K) :
    T.symm Y = a⁻¹ * Y * b⁻¹ := by
  obtain ⟨hda, hdb⟩ := isUnit_det_of_bimul hT
  rw [LinearEquiv.symm_apply_eq, hT]
  calc Y = (a * a⁻¹) * Y * (b⁻¹ * b) := by
        rw [Matrix.mul_nonsing_inv a hda, Matrix.nonsing_inv_mul b hdb]; simp
    _ = a * (a⁻¹ * Y * b⁻¹) * b := by simp only [Matrix.mul_assoc]

@[expose] def bimulGrp : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) where
  carrier := {T | ∃ a b : Matrix (Fin 2) (Fin 2) K, ∀ X, T X = a * X * b}
  mul_mem' := by
    rintro S T ⟨a, b, hS⟩ ⟨a', b', hT⟩
    exact ⟨a * a', b' * b, fun X => by rw [LinearEquiv.mul_apply, hT, hS]; simp [Matrix.mul_assoc]⟩
  one_mem' := ⟨1, 1, fun X => by simp⟩
  inv_mem' := by
    rintro T ⟨a, b, hT⟩
    exact ⟨a⁻¹, b⁻¹, fun Y => symm_apply_of_bimul hT Y⟩

theorem mem_bimulGrp {T : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K} :
    T ∈ bimulGrp ↔ ∃ a b : Matrix (Fin 2) (Fin 2) K, ∀ X, T X = a * X * b := Iff.rfl

theorem commute_leftGrp_rightGrp : ∀ x ∈ (leftGrp : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K]
    Matrix (Fin 2) (Fin 2) K)), ∀ y ∈ (rightGrp : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K]
    Matrix (Fin 2) (Fin 2) K)), x * y = y * x := by
  rintro x ⟨A, hA⟩ y ⟨B, hB⟩
  refine LinearEquiv.ext fun X => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hB, hA, hB, hA, Matrix.mul_assoc]

theorem specialOrthogonalGroup_le_bimulGrp (h2 : (2 : K) ≠ 0) :
    TauCeti.QuadraticMap.specialOrthogonalGroup (detQ (K := K)) ≤ bimulGrp (K := K) := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have h := TauCeti.QuadraticMap.specialOrthogonalGroup_le_of_reflection_mul_mem
    (detQ (K := K)) nondegenerate_detQ (bimulGrp (K := K)).toSubmonoid (fun v w hv hw => by
      have hdv := det_ne_zero_of_invertible hv
      have hdw := det_ne_zero_of_invertible hw
      refine ⟨((v.det * w.det)⁻¹ : K) • (v * adjugate w), adjugate w * v, fun X => ?_⟩
      rw [LinearEquiv.mul_apply, reflection_detQ_apply, reflection_detQ_apply]
      exact reflM_reflM_eq hdv hdw X)
  exact fun g hg => h hg

theorem commutator_bimulGrp_le :
    ⁅bimulGrp (K := K), bimulGrp⁆ ≤ mulSub (leftGrp (K := K)) rightGrp
      commute_leftGrp_rightGrp := by
  refine Subgroup.commutator_le.mpr fun S hS T hT => ?_
  obtain ⟨a, b, hSab⟩ := hS
  obtain ⟨a', b', hTab⟩ := hT
  obtain ⟨hda, hdb⟩ := isUnit_det_of_bimul hSab
  obtain ⟨hda', hdb'⟩ := isUnit_det_of_bimul hTab
  have hdet : ∀ {x y : Matrix (Fin 2) (Fin 2) K}, IsUnit x.det → IsUnit y.det →
      (x * y * x⁻¹ * y⁻¹).det = 1 := by
    intro x y hx hy
    have hx' : x.det ≠ 0 := hx.ne_zero
    have hy' : y.det ≠ 0 := hy.ne_zero
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
      Matrix.det_nonsing_inv]
    simp only [Ring.inverse_eq_inv']
    field_simp
  have hdet' : ∀ {x y : Matrix (Fin 2) (Fin 2) K}, IsUnit x.det → IsUnit y.det →
      (x⁻¹ * y⁻¹ * x * y).det = 1 := by
    intro x y hx hy
    have hx' : x.det ≠ 0 := hx.ne_zero
    have hy' : y.det ≠ 0 := hy.ne_zero
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
      Matrix.det_nonsing_inv]
    simp only [Ring.inverse_eq_inv']
    field_simp
  refine ⟨lmulEquiv (⟨a * a' * a⁻¹ * a'⁻¹, hdet hda hda'⟩ : SL(2, K)), lmulEquiv_mem_leftGrp _,
    rmulEquiv (⟨b'⁻¹ * b⁻¹ * b' * b, hdet' hdb' hdb⟩ : SL(2, K)), rmulEquiv_mem_rightGrp _, ?_⟩
  refine LinearEquiv.ext fun X => ?_
  rw [commutatorElement_def]
  simp only [LinearEquiv.mul_apply]
  have e1 : (S⁻¹ : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) =
      S.symm := rfl
  have e2 : (T⁻¹ : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) =
      T.symm := rfl
  rw [e1, e2, symm_apply_of_bimul hTab, symm_apply_of_bimul hSab, hTab, hSab]
  change _ = (a * a' * a⁻¹ * a'⁻¹) * (X * (b'⁻¹ * b⁻¹ * b' * b))
  simp only [Matrix.mul_assoc]

theorem le_mulSub_of_isPerfect (h2 : (2 : K) ≠ 0)
    {S : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)} (hS : ⁅S, S⁆ = S)
    (hSO : S ≤ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) :
    S ≤ mulSub (leftGrp (K := K)) rightGrp commute_leftGrp_rightGrp := by
  have hdet : S ≤ TauCeti.QuadraticMap.specialOrthogonalGroup (detQ (K := K)) := by
    intro g hg
    refine TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr ⟨hSO hg, ?_⟩
    have : g ∈ ⁅S, S⁆ := by rw [hS]; exact hg
    have hker : ⁅S, S⁆ ≤ (LinearEquiv.det :
        (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) →* Kˣ).ker := by
      refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact (commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _))
    exact MonoidHom.mem_ker.mp (hker this)
  calc S = ⁅S, S⁆ := hS.symm
    _ ≤ ⁅bimulGrp (K := K), bimulGrp⁆ :=
      Subgroup.commutator_mono (hdet.trans (specialOrthogonalGroup_le_bimulGrp h2))
        (hdet.trans (specialOrthogonalGroup_le_bimulGrp h2))
    _ ≤ _ := commutator_bimulGrp_le

end CFSG.ClassicalInvolution.ModelFacts
