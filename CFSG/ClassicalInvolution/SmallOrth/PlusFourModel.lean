module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Coord

variable {P P' : HypPair Q}

@[expose] noncomputable def coord (P P' : HypPair Q) : Matrix (Fin 2) (Fin 2) K →ₗ[K] V where
  toFun m := m 0 0 • P.e + m 1 1 • P.f + m 0 1 • P'.e - m 1 0 • P'.f
  map_add' m n := by
    simp only [Matrix.add_apply, add_smul]
    module
  map_smul' c m := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    module

theorem coord_apply (m : Matrix (Fin 2) (Fin 2) K) :
    coord P P' m = m 0 0 • P.e + m 1 1 • P.f + m 0 1 • P'.e - m 1 0 • P'.f :=
  rfl

theorem map_comb (h : P.Orth P') (a d b c : K) :
    Q (a • P.e + d • P.f + b • P'.e + c • P'.f) = a * d + b * c := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_add Q]
  simp only [map_smul_eq_sq, polar_add_left, polar_smul_left_eq, polar_smul_right_eq, P.Q_e,
    P.Q_f, P'.Q_e, P'.Q_f, P.polar_ef, P'.polar_ef, h.ee, h.ef, h.fe, h.ff]
  ring

theorem map_coord (h : P.Orth P') (m : Matrix (Fin 2) (Fin 2) K) :
    Q (coord P P' m) = m.det := by
  rw [coord_apply, sub_eq_add_neg, ← neg_smul, map_comb h, Matrix.det_fin_two]
  ring

@[expose] def pol (m n : Matrix (Fin 2) (Fin 2) K) : K :=
  m 0 0 * n 1 1 + m 1 1 * n 0 0 - m 0 1 * n 1 0 - m 1 0 * n 0 1

theorem polar_coord (h : P.Orth P') (m n : Matrix (Fin 2) (Fin 2) K) :
    polar Q (coord P P' m) (coord P P' n) = pol m n := by
  rw [polar, ← map_add, map_coord h, map_coord h, map_coord h, Matrix.det_fin_two,
    Matrix.det_fin_two, Matrix.det_fin_two, pol]
  simp only [Matrix.add_apply]
  ring

theorem eichler_coord (h : P.Orth P') {u w : Matrix (Fin 2) (Fin 2) K} (hu : u.det = 0)
    (huw : pol u w = 0) (m : Matrix (Fin 2) (Fin 2) K) :
    eichler Q (coord P P' u) (coord P P' w) (coord P P' m) =
      coord P P' (m + pol m u • w - (pol m w + w.det * pol m u) • u) := by
  rw [eichler_apply (by rw [map_coord h, hu]) (by rw [polar_coord h, huw]), polar_coord h,
    polar_coord h, map_coord h]
  simp only [map_sub, map_add, map_smul]

theorem coord_injective (h : P.Orth P') : Function.Injective (coord P P' (K := K)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  have h1 := congrArg (fun z => polar Q z P.f) hm
  have h2 := congrArg (fun z => polar Q z P.e) hm
  have h3 := congrArg (fun z => polar Q z P'.f) hm
  have h4 := congrArg (fun z => polar Q z P'.e) hm
  have hs := h.symm
  simp only [coord_apply, polar_sub_left, polar_add_left, polar_smul_left_eq, polar_zero_left,
    P.polar_ef, P.polar_fe, P.polar_ee, P.polar_ff, P'.polar_ef, P'.polar_fe, P'.polar_ee,
    P'.polar_ff, h.ee, h.ef, h.fe, h.ff, hs.ee, hs.ef, hs.fe, hs.ff, mul_zero, mul_one, add_zero,
    zero_add, sub_zero] at h1 h2 h3 h4
  ext i j
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h3
  · simpa using h4
  · exact h2

theorem coord_E11 : coord P P' (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) = P.e := by
  simp [coord_apply]

theorem coord_E22 : coord P P' (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) = P.f := by
  simp [coord_apply]

theorem coord_E12 : coord P P' (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K) = P'.e := by
  simp [coord_apply]

theorem coord_E21 : coord P P' (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K) = -P'.f := by
  simp [coord_apply]

end Coord

section Hom

open scoped MatrixGroups

@[expose] def lmul (A : SL(2, K)) :
    Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  LinearEquiv.ofLinearMap (LinearMap.mulLeft K (A : Matrix (Fin 2) (Fin 2) K))
    (LinearMap.mulLeft K ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))
    (LinearMap.ext fun m => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
        ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul])
    (LinearMap.ext fun m => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
        ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul])

@[expose] def rmul (B : SL(2, K)) :
    Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  LinearEquiv.ofLinearMap (LinearMap.mulRight K ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))
    (LinearMap.mulRight K (B : Matrix (Fin 2) (Fin 2) K))
    (LinearMap.ext fun m => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.id_apply,
        Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one])
    (LinearMap.ext fun m => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.id_apply,
        Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one])

theorem lmul_apply (A : SL(2, K)) (m : Matrix (Fin 2) (Fin 2) K) : lmul A m = A * m := rfl

theorem rmul_apply (B : SL(2, K)) (m : Matrix (Fin 2) (Fin 2) K) :
    rmul B m = m * (B⁻¹ : SL(2, K)) := rfl

@[expose] def lmulHom :
    SL(2, K) →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) where
  toFun := lmul
  map_one' := LinearEquiv.ext fun m => by
    rw [lmul_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    rfl
  map_mul' A B := LinearEquiv.ext fun m => by
    rw [LinearEquiv.mul_apply, lmul_apply, lmul_apply, lmul_apply,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

@[expose] def rmulHom :
    SL(2, K) →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) where
  toFun := rmul
  map_one' := LinearEquiv.ext fun m => by
    rw [rmul_apply, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
    rfl
  map_mul' A B := LinearEquiv.ext fun m => by
    rw [LinearEquiv.mul_apply, rmul_apply, rmul_apply, rmul_apply, mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

@[expose] def conjHom {W : Type*} [AddCommGroup W] [Module K W]
    (e : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] W) :
    (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) →* (W ≃ₗ[K] W) where
  toFun g := e.symm.trans (g.trans e)
  map_one' := LinearEquiv.ext fun x => by simp
  map_mul' g₁ g₂ := LinearEquiv.ext fun x => by simp

theorem conjHom_apply {W : Type*} [AddCommGroup W] [Module K W]
    (e : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] W)
    (g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) (x : W) :
    conjHom e g x = e (g (e.symm x)) := rfl

end Hom

end CFSG.ClassicalGroups.Orthogonal.Small
