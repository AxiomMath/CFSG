module

public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Quasithin.G11.P3Ortho.Om4 (toMat det_toMat rho' commutator_eq_range rho'_injective
  isPerfect_prod)

variable (K : Type) [Field K]

@[expose] noncomputable def detCoord : (Fin (2 * 2) → K) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  (LinearEquiv.funCongrLeft K K (plusIndexEquiv 2)).trans (toMat K)

theorem det_detCoord (v : Fin (2 * 2) → K) : (detCoord K v).det = coordinateQuadPlus 2 K v := by
  rw [detCoord, LinearEquiv.trans_apply, det_toMat, coordinateQuadPlus_apply]
  rfl

@[expose] noncomputable def detConj :
    ((Fin (2 * 2) → K) ≃ₗ[K] (Fin (2 * 2) → K)) ≃*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) where
  toFun g := ((detCoord K).symm.trans g).trans (detCoord K)
  invFun g := ((detCoord K).trans g).trans (detCoord K).symm
  left_inv g := by
    ext v
    simp
  right_inv g := by
    ext Z
    simp
  map_mul' g g' := by
    ext Z
    simp

theorem detConj_apply (g : (Fin (2 * 2) → K) ≃ₗ[K] (Fin (2 * 2) → K))
    (Z : Matrix (Fin 2) (Fin 2) K) : detConj K g Z = detCoord K (g ((detCoord K).symm Z)) :=
  rfl

theorem detConj_symm_apply (g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (v : Fin (2 * 2) → K) : (detConj K).symm g v = (detCoord K).symm (g (detCoord K v)) :=
  rfl

theorem detCoord_apply_eq (g : (Fin (2 * 2) → K) ≃ₗ[K] (Fin (2 * 2) → K)) (v : Fin (2 * 2) → K) :
    detCoord K (g v) = detConj K g (detCoord K v) := by
  rw [detConj_apply, LinearEquiv.symm_apply_apply]

theorem detConj_mem_iff (g : (Fin (2 * 2) → K) ≃ₗ[K] (Fin (2 * 2) → K)) :
    detConj K g ∈ DeterminantIsometries K ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 2 K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro h v
    have h1 := h (detCoord K v)
    rw [determinantForm_apply, determinantForm_apply, ← detCoord_apply_eq, det_detCoord,
      det_detCoord] at h1
    exact h1
  · intro h Z
    rw [determinantForm_apply, determinantForm_apply, detConj_apply, det_detCoord, h,
      ← det_detCoord, LinearEquiv.apply_symm_apply]

theorem map_orthogonalGroup_detConj :
    (TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 2 K)).map
        (detConj K : ((Fin (2 * 2) → K) ≃ₗ[K] (Fin (2 * 2) → K)) →*
          (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)) =
      DeterminantIsometries K := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact (detConj_mem_iff K g').mpr hg'
  · intro hg
    refine ⟨(detConj K).symm g, (detConj_mem_iff K _).mp ?_, ?_⟩
    · rw [MulEquiv.apply_symm_apply]
      exact hg
    · exact MulEquiv.apply_symm_apply _ _

variable [Finite K] [CharP K 2]

theorem map_orthDerived_detConj (h4 : 4 ≤ Nat.card K) :
    (orthDerived (coordinateQuadPlus 2 K)).map
        (detConj K : ((Fin (2 * 2) → K) ≃ₗ[K] (Fin (2 * 2) → K)) →*
          (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)) = (rho' K).range := by
  rw [orthDerived, Subgroup.map_commutator, map_orthogonalGroup_detConj, commutator_eq_range h4]

@[expose] noncomputable def orthTwoEquiv (h4 : 4 ≤ Nat.card K) :
    orthDerived (coordinateQuadPlus 2 K) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
  ((detConj K).subgroupMap (orthDerived (coordinateQuadPlus 2 K))).trans
    ((MulEquiv.subgroupCongr (map_orthDerived_detConj K h4)).trans
      (MonoidHom.ofInjective (rho'_injective (K := K))).symm)

theorem rho'_orthTwoEquiv (h4 : 4 ≤ Nat.card K) (g : orthDerived (coordinateQuadPlus 2 K)) :
    rho' K (orthTwoEquiv K h4 g) = detConj K g := by
  rw [orthTwoEquiv]
  simp only [MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem isPerfect_orthDerived_two (h4 : 4 ≤ Nat.card K) :
    Group.IsPerfect (orthDerived (coordinateQuadPlus 2 K)) := by
  have hSL := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) := isPerfect_prod hSL hSL
  exact Group.IsPerfect.ofSurjective (f := (orthTwoEquiv K h4).symm.toMonoidHom)
    (orthTwoEquiv K h4).symm.surjective

omit [Finite K] [CharP K 2] in
theorem rho'_apply (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (Z : Matrix (Fin 2) (Fin 2) K) :
    rho' K z Z = (z.1 : Matrix (Fin 2) (Fin 2) K) * Z *
      ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  specialRho_apply z Z

omit [Finite K] [CharP K 2] in
theorem sl2_mul_self_sub_trace_smul_add_one (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (A : Matrix (Fin 2) (Fin 2) K) * A -
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) • (A : Matrix (Fin 2) (Fin 2) K) + 1 = 0 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination -hdet

omit [Finite K] [CharP K 2] in
theorem trace_sl2_inv (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.trace ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.trace (B : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.trace_fin_two]
  simp [add_comm]

omit [Finite K] [CharP K 2] in
theorem rel_left (A : Matrix.SpecialLinearGroup (Fin 2) K) (w : Fin (2 * 2) → K) :
    (detConj K).symm (rho' K (A, 1)) ((detConj K).symm (rho' K (A, 1)) w) -
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) • (detConj K).symm (rho' K (A, 1)) w + w = 0 := by
  apply (detCoord K).injective
  rw [map_add, map_sub, map_smul, detConj_symm_apply, detConj_symm_apply]
  simp only [LinearEquiv.apply_symm_apply, map_zero, rho'_apply, inv_one,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  have key := congrArg (· * detCoord K w) (sl2_mul_self_sub_trace_smul_add_one K A)
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.zero_mul,
    Matrix.mul_assoc] at key
  exact key

omit [Finite K] [CharP K 2] in
theorem rel_right (B : Matrix.SpecialLinearGroup (Fin 2) K) (w : Fin (2 * 2) → K) :
    (detConj K).symm (rho' K (1, B)) ((detConj K).symm (rho' K (1, B)) w) -
      Matrix.trace (B : Matrix (Fin 2) (Fin 2) K) • (detConj K).symm (rho' K (1, B)) w + w = 0 := by
  apply (detCoord K).injective
  rw [map_add, map_sub, map_smul, detConj_symm_apply, detConj_symm_apply]
  simp only [LinearEquiv.apply_symm_apply, map_zero, rho'_apply,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  have key := congrArg (detCoord K w * ·) (sl2_mul_self_sub_trace_smul_add_one K B⁻¹)
  rw [trace_sl2_inv] at key
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_zero,
    ← Matrix.mul_assoc] at key
  exact key

end CFSG.SeitzReduction.OmegaPilot
