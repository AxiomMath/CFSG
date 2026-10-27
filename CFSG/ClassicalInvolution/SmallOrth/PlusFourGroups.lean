module

public import CFSG.ClassicalInvolution.SmallOrth.PlusFourModel

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap
open scoped MatrixGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [FiniteDimensional K V] {P P' : HypPair Q}

section Theta

variable (h : P.Orth P') (hdim : Module.finrank K V = 4)

theorem coord_surjective (h : P.Orth P') (hdim : Module.finrank K V = 4) :
    Function.Surjective (coord P P' (K := K)) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hdim, Module.finrank_matrix]; simp)).mp
    (coord_injective h)

@[expose] noncomputable def coordEquiv (h : P.Orth P') (hdim : Module.finrank K V = 4) :
    Matrix (Fin 2) (Fin 2) K ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coord P P') ⟨coord_injective h, coord_surjective h hdim⟩

theorem coordEquiv_apply (m : Matrix (Fin 2) (Fin 2) K) : coordEquiv h hdim m = coord P P' m :=
  rfl

@[expose] noncomputable def thetaL : SL(2, K) →* (V ≃ₗ[K] V) :=
  (conjHom (coordEquiv h hdim)).comp lmulHom

@[expose] noncomputable def thetaR : SL(2, K) →* (V ≃ₗ[K] V) :=
  (conjHom (coordEquiv h hdim)).comp rmulHom

theorem thetaL_apply (A : SL(2, K)) (m : Matrix (Fin 2) (Fin 2) K) :
    thetaL h hdim A (coord P P' m) = coord P P' (A * m) := by
  change coordEquiv h hdim (lmul A ((coordEquiv h hdim).symm (coordEquiv h hdim m))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem thetaR_apply (B : SL(2, K)) (m : Matrix (Fin 2) (Fin 2) K) :
    thetaR h hdim B (coord P P' m) = coord P P' (m * (B⁻¹ : SL(2, K))) := by
  change coordEquiv h hdim (rmul B ((coordEquiv h hdim).symm (coordEquiv h hdim m))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem thetaL_mem_orthogonalGroup (A : SL(2, K)) :
    thetaL h hdim A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  rw [thetaL_apply, map_coord h, map_coord h, Matrix.det_mul, A.det_coe, one_mul]

theorem thetaR_mem_orthogonalGroup (B : SL(2, K)) :
    thetaR h hdim B ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  rw [thetaR_apply, map_coord h, map_coord h, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
    mul_one]

theorem thetaL_thetaR_comm (A B : SL(2, K)) :
    thetaL h hdim A * thetaR h hdim B = thetaR h hdim B * thetaL h hdim A := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, thetaR_apply, thetaL_apply, thetaL_apply,
    thetaR_apply, Matrix.mul_assoc]

theorem thetaL_injective : Function.Injective (thetaL h hdim) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : thetaL h hdim A (coord P P' 1) = coord P P' 1 := by rw [hA]; rfl
  rw [thetaL_apply, Matrix.mul_one] at h1
  exact Subtype.ext (coord_injective h h1)

theorem thetaR_injective : Function.Injective (thetaR h hdim) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have h1 : thetaR h hdim B (coord P P' 1) = coord P P' 1 := by rw [hB]; rfl
  rw [thetaR_apply, Matrix.one_mul] at h1
  have h2 := coord_injective h h1
  have : (B⁻¹ : SL(2, K)) = 1 := Subtype.ext h2
  exact inv_eq_one.mp this

theorem thetaL_transvection_zero_one (c : K) :
    thetaL h hdim (Matrix.SpecialLinearGroup.transvection zero_ne_one c) =
      eichler Q P.e (c • P'.e) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  have key := eichler_coord h (u := !![1, 0; 0, 0]) (w := c • !![0, 1; 0, 0])
    (by simp [Matrix.det_fin_two]) (by simp [pol]) m
  rw [coord_E11, map_smul, coord_E12] at key
  rw [thetaL_apply, key]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, pol, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply] <;> ring

theorem thetaL_transvection_one_zero (c : K) :
    thetaL h hdim (Matrix.SpecialLinearGroup.transvection one_ne_zero c) =
      eichler Q P'.f (c • P.f) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  have hf' : P'.f = coord P P' (!![0, 0; -1, 0] : Matrix (Fin 2) (Fin 2) K) := by
    simp [coord_apply]
  have key := eichler_coord h (u := !![0, 0; -1, 0]) (w := c • !![0, 0; 0, 1])
    (by simp [Matrix.det_fin_two]) (by simp [pol]) m
  rw [← hf', map_smul, coord_E22] at key
  rw [thetaL_apply, key]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, pol, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply] <;> ring

theorem thetaR_transvection_zero_one (c : K) :
    thetaR h hdim (Matrix.SpecialLinearGroup.transvection zero_ne_one c) =
      eichler Q P.f ((-c) • P'.e) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  have key := eichler_coord h (u := !![0, 0; 0, 1]) (w := (-c) • !![0, 1; 0, 0])
    (by simp [Matrix.det_fin_two]) (by simp [pol]) m
  rw [coord_E22, map_smul, coord_E12] at key
  rw [thetaR_apply, key]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.SpecialLinearGroup.transvection_coe, pol, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem thetaR_transvection_one_zero (c : K) :
    thetaR h hdim (Matrix.SpecialLinearGroup.transvection one_ne_zero c) =
      eichler Q P'.f ((-c) • P.e) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  have hf' : P'.f = coord P P' (!![0, 0; -1, 0] : Matrix (Fin 2) (Fin 2) K) := by
    simp [coord_apply]
  have key := eichler_coord h (u := !![0, 0; -1, 0]) (w := (-c) • !![1, 0; 0, 0])
    (by simp [Matrix.det_fin_two]) (by simp [pol]) m
  rw [← hf', map_smul, coord_E11] at key
  rw [thetaR_apply, key]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.SpecialLinearGroup.transvection_coe, pol, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

end Theta

end CFSG.ClassicalGroups.Orthogonal.Small
