module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4NSAlg
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Mat

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp

open QuadraticAlgebra CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]



@[expose] def omE : QE F := ⟨0, 1⟩

theorem omE_mul_self : (omE : QE F) * omE = -1 :=
  QuadraticAlgebra.ext (by simp [omE]) (by simp [omE])

theorem star_omE : star (omE : QE F) = -omE := QuadraticAlgebra.ext (by simp [omE]) (by simp [omE])

theorem star_algebraMap (x : F) : star (algebraMap F (QE F) x) = algebraMap F (QE F) x :=
  QuadraticAlgebra.ext (by simp) (by simp)

@[expose] def Jm (R : Type) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

theorem Jm_mul_Jm {R : Type} [CommRing R] : Jm R * Jm R = -1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def ratM (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) (QE F) :=
  B.map (algebraMap F (QE F))

theorem ratM_mul (B B' : Matrix (Fin 2) (Fin 2) F) : ratM (B * B') = ratM B * ratM B' := by
  simp [ratM]

theorem ratM_one : ratM (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by simp [ratM]

theorem ratM_conjTranspose (B : Matrix (Fin 2) (Fin 2) F) : (ratM B)ᴴ = (ratM B)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp [ratM, Matrix.conjTranspose_apply, star_algebraMap]

theorem ratM_det (B : Matrix (Fin 2) (Fin 2) F) : (ratM B).det = algebraMap F (QE F) B.det := by
  have := RingHom.map_det (algebraMap F (QE F)) B
  rw [RingHom.mapMatrix_apply] at this
  exact this.symm

theorem transpose_J_mul {R : Type} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) :
    Xᵀ * Jm R * X = X.det • Jm R := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

@[expose] def Pm (lam : QE F) : Matrix (Fin 2) (Fin 2) (QE F) := !![1, omE; lam, -(lam * omE)]

theorem Pm_conjTranspose_mul {lam : QE F} (hlam : star lam * lam = -1) :
    (Pm lam)ᴴ * Pm lam = ((2 : QE F) * omE) • Jm (QE F) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Jm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, star_omE]
  · linear_combination hlam
  · linear_combination (-omE) * hlam
  · linear_combination omE * hlam
  · linear_combination (-(omE * omE)) * hlam

@[expose] def halfE (F : Type) [Field F] : QE F := algebraMap F (QE F) (2⁻¹ : F)

theorem two_mul_halfE (h2 : (2 : F) ≠ 0) : (2 : QE F) * halfE F = 1 := by
  have h : (2 : QE F) = algebraMap F (QE F) 2 := (map_ofNat (algebraMap F (QE F)) 2).symm
  rw [h, halfE, ← map_mul, mul_inv_cancel₀ h2, map_one]

@[expose] def Pinv (F : Type) [Field F] (lam : QE F) : Matrix (Fin 2) (Fin 2) (QE F) :=
  (halfE F * omE) • (Jm (QE F) * (Pm lam)ᴴ)

theorem Pinv_mul_Pm (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1) :
    Pinv F lam * Pm lam = 1 := by
  rw [Pinv, Matrix.smul_mul, Matrix.mul_assoc, Pm_conjTranspose_mul hlam, Matrix.mul_smul,
    Jm_mul_Jm]
  have h2' := two_mul_halfE h2
  have : halfE F * (omE : QE F) * (2 * (omE : QE F)) = -1 := by
    linear_combination ((omE : QE F) * omE) * h2' + omE_mul_self (F := F)
  rw [smul_smul, this]
  simp

theorem Pm_mul_Pinv (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1) :
    Pm lam * Pinv F lam = 1 :=
  mul_eq_one_comm.mp (Pinv_mul_Pm h2 hlam)


theorem conj_eq_det_smul' {M : Matrix (Fin 2) (Fin 2) (QE F)}
    (h : Mᴴ * Jm (QE F) * M = Jm (QE F)) : M.map star = (M.map star).det • M := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Jm, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two]
  · linear_combination star (M 0 0) * e10 - star (M 0 1) * e00
  · linear_combination star (M 0 0) * e11 - star (M 0 1) * e01
  · linear_combination (-(star (M 1 1))) * e00 + (star (M 1 0)) * e10
  · linear_combination star (M 1 0) * e11 - star (M 1 1) * e01


theorem unit_two_om (h2 : (2 : F) ≠ 0) :
    (-(halfE F * (omE : QE F))) * ((2 : QE F) * omE) = 1 := by
  have h2' := two_mul_halfE h2
  linear_combination (-((omE : QE F) * omE)) * h2' - omE_mul_self (F := F)

theorem Pinv_conj_J (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1) :
    ((2 : QE F) * omE) • ((Pinv F lam)ᴴ * Jm (QE F) * Pinv F lam) = 1 := by
  have h1 := Pm_mul_Pinv h2 hlam
  calc ((2 : QE F) * omE) • ((Pinv F lam)ᴴ * Jm (QE F) * Pinv F lam)
      = (Pinv F lam)ᴴ * (((2 : QE F) * omE) • Jm (QE F)) * Pinv F lam := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = (Pinv F lam)ᴴ * ((Pm lam)ᴴ * Pm lam) * Pinv F lam := by rw [Pm_conjTranspose_mul hlam]
    _ = (Pm lam * Pinv F lam)ᴴ * (Pm lam * Pinv F lam) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1]; simp

theorem unitary_conj_J (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1)
    {N : Matrix (Fin 2) (Fin 2) (QE F)} (hN : Nᴴ * N = 1) :
    (Pinv F lam * N * Pm lam)ᴴ * Jm (QE F) * (Pinv F lam * N * Pm lam) = Jm (QE F) := by
  set c : QE F := (2 : QE F) * omE with hc
  set κ : QE F := -(halfE F * (omE : QE F)) with hκ
  have hunit : κ * c = 1 := unit_two_om (F := F) h2
  set X := (Pinv F lam * N * Pm lam)ᴴ * Jm (QE F) * (Pinv F lam * N * Pm lam) with hX
  have key : c • X = c • Jm (QE F) := by
    calc c • X
        = (Pm lam)ᴴ * Nᴴ * (c • ((Pinv F lam)ᴴ * Jm (QE F) * Pinv F lam)) * N * Pm lam := by
          simp only [hX, Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc]
      _ = (Pm lam)ᴴ * Pm lam := by
          rw [hc, Pinv_conj_J h2 hlam]
          simp [Matrix.mul_assoc, hN]
      _ = c • Jm (QE F) := Pm_conjTranspose_mul hlam
  calc X = (κ * c) • X := by rw [hunit, one_smul]
    _ = κ • (c • X) := by rw [smul_smul]
    _ = κ • (c • Jm (QE F)) := by rw [key]
    _ = (κ * c) • Jm (QE F) := by rw [smul_smul]
    _ = Jm (QE F) := by rw [hunit, one_smul]

theorem det_Pinv_mul (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1) :
    (Pinv F lam).det * (Pm lam).det = 1 := by
  rw [← Matrix.det_mul, Pinv_mul_Pm h2 hlam, Matrix.det_one]

theorem star_det {M : Matrix (Fin 2) (Fin 2) (QE F)} :
    (M.map star).det = star M.det := by
  have h := RingHom.map_det (starRingEnd (QE F)) M
  have hf : ((starRingEnd (QE F)) : QE F → QE F) = star := funext fun x => starRingEnd_apply x
  rw [RingHom.mapMatrix_apply, hf] at h
  exact h.symm

theorem im_eq_zero_of_star_eq (h2 : (2 : F) ≠ 0) {z : QE F} (h : star z = z) : z.im = 0 := by
  have := congrArg QuadraticAlgebra.im h
  rw [QuadraticAlgebra.im_star] at this
  have h3 : (2 : F) * z.im = 0 := by linear_combination -this
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem eq_algebraMap_of_im {z : QE F} (h : z.im = 0) : z = algebraMap F (QE F) z.re :=
  QuadraticAlgebra.ext (by simp) (by simp [h])

theorem exists_rat_of_unitary (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1)
    {N : Matrix (Fin 2) (Fin 2) (QE F)} (hN : Nᴴ * N = 1) (hdet : N.det = 1) :
    ∃ B : SL(2, F), N = Pm lam * ratM (B : Matrix (Fin 2) (Fin 2) F) * Pinv F lam := by
  set N' := Pinv F lam * N * Pm lam with hN'
  have hJ := unitary_conj_J h2 hlam hN
  have hdet' : N'.det = 1 := by
    have h1 := det_Pinv_mul h2 hlam
    rw [hN', Matrix.det_mul, Matrix.det_mul, hdet]
    linear_combination h1
  have hconj := conj_eq_det_smul' hJ
  rw [star_det, hdet', star_one, one_smul] at hconj
  have him : ∀ i j, (N' i j).im = 0 := fun i j => im_eq_zero_of_star_eq h2 (by
    have := congrFun (congrFun hconj i) j
    simpa using this)
  have hrat : N' = ratM (N'.map QuadraticAlgebra.re) := by
    refine Matrix.ext fun i j => ?_
    simp only [ratM, Matrix.map_apply]
    exact eq_algebraMap_of_im (him i j)
  have hdetB : (N'.map QuadraticAlgebra.re).det = 1 := by
    have h3 := ratM_det (N'.map QuadraticAlgebra.re)
    rw [← hrat, hdet'] at h3
    have h4 : algebraMap F (QE F) ((N'.map QuadraticAlgebra.re).det) = algebraMap F (QE F) 1 := by
      rw [← h3, map_one]
    exact (algebraMap F (QE F)).injective h4
  refine ⟨⟨N'.map QuadraticAlgebra.re, hdetB⟩, ?_⟩
  show N = Pm lam * ratM (N'.map QuadraticAlgebra.re) * Pinv F lam
  rw [← hrat, hN']
  have h1 := Pm_mul_Pinv h2 hlam
  calc N = (Pm lam * Pinv F lam) * N * (Pm lam * Pinv F lam) := by rw [h1]; simp
    _ = Pm lam * (Pinv F lam * N * Pm lam) * Pinv F lam := by simp only [Matrix.mul_assoc]

@[expose] def Xm (lam : QE F) (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) (QE F) :=
  Pm lam * ratM B * Pinv F lam

theorem Xm_mul (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1)
    (B B' : Matrix (Fin 2) (Fin 2) F) : Xm lam (B * B') = Xm lam B * Xm lam B' := by
  have h1 := Pinv_mul_Pm h2 hlam
  calc Xm lam (B * B') = Pm lam * (ratM B * ratM B') * Pinv F lam := by rw [Xm, ratM_mul]
    _ = Pm lam * ratM B * (Pinv F lam * Pm lam) * ratM B' * Pinv F lam := by
        rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = Xm lam B * Xm lam B' := by simp only [Xm, Matrix.mul_assoc]

theorem Xm_one (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1) :
    Xm lam 1 = 1 := by
  rw [Xm, ratM_one, Matrix.mul_one, Pm_mul_Pinv h2 hlam]

theorem Xm_det (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1)
    {B : Matrix (Fin 2) (Fin 2) F} (hB : B.det = 1) : (Xm lam B).det = 1 := by
  rw [Xm, Matrix.det_mul, Matrix.det_mul, ratM_det, hB, map_one]
  have h1 := det_Pinv_mul h2 hlam
  linear_combination h1

theorem Xm_unitary (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1)
    {B : Matrix (Fin 2) (Fin 2) F} (hB : B.det = 1) : (Xm lam B)ᴴ * Xm lam B = 1 := by
  have hc := Pinv_conj_J h2 hlam
  have hBJ : (ratM B)ᵀ * Jm (QE F) * ratM B = Jm (QE F) := by
    rw [transpose_J_mul, ratM_det, hB, map_one, one_smul]
  set c : QE F := (2 : QE F) * omE with hcdef
  calc (Xm lam B)ᴴ * Xm lam B
      = (Pinv F lam)ᴴ * (ratM B)ᴴ * ((Pm lam)ᴴ * Pm lam) * ratM B * Pinv F lam := by
        simp only [Xm, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = c • ((Pinv F lam)ᴴ * ((ratM B)ᵀ * Jm (QE F) * ratM B) * Pinv F lam) := by
        rw [Pm_conjTranspose_mul hlam, ratM_conjTranspose]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        rfl
    _ = 1 := by rw [hBJ]; simpa [Matrix.mul_assoc] using hc

theorem Xm_injective (h2 : (2 : F) ≠ 0) {lam : QE F} (hlam : star lam * lam = -1)
    {B B' : Matrix (Fin 2) (Fin 2) F} (h : Xm lam B = Xm lam B') : B = B' := by
  have h1 := Pinv_mul_Pm h2 hlam
  have h3 : Pinv F lam * Xm lam B * Pm lam = ratM B := by
    simp only [Xm]
    calc Pinv F lam * (Pm lam * ratM B * Pinv F lam) * Pm lam
        = (Pinv F lam * Pm lam) * ratM B * (Pinv F lam * Pm lam) := by simp only [Matrix.mul_assoc]
      _ = ratM B := by rw [h1]; simp
  have h4 : Pinv F lam * Xm lam B' * Pm lam = ratM B' := by
    simp only [Xm]
    calc Pinv F lam * (Pm lam * ratM B' * Pinv F lam) * Pm lam
        = (Pinv F lam * Pm lam) * ratM B' * (Pinv F lam * Pm lam) := by simp only [Matrix.mul_assoc]
      _ = ratM B' := by rw [h1]; simp
  have h5 : ratM B = ratM B' := by rw [← h3, ← h4, h]
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h5 i) j
  simp only [ratM, Matrix.map_apply] at this
  exact (algebraMap F (QE F)).injective this


theorem exists_lam [Finite F] (h2 : (2 : F) ≠ 0) : ∃ lam : QE F, star lam * lam = -1 := by
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq h2 (-1 : F)
  refine ⟨⟨a, b⟩, QuadraticAlgebra.ext ?_ ?_⟩
  · simp
    linear_combination hab
  · simp
    ring

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
