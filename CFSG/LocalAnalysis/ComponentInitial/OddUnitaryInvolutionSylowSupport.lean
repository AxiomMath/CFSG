module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

open Matrix

variable {K : Type*} [Field K]

section Supp

variable {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[expose] def suppMat (E : Matrix ι κ K) (F : Matrix κ ι K) (M : Matrix κ κ K) :
    Matrix ι ι K :=
  1 + E * (M - 1) * F

variable {E : Matrix ι κ K} {F : Matrix κ ι K}

theorem suppMat_one : suppMat E F 1 = 1 := by
  simp [suppMat]

theorem suppMat_mul [Fintype ι] (hFE : F * E = 1) (M M' : Matrix κ κ K) :
    suppMat E F (M * M') = suppMat E F M * suppMat E F M' := by
  have h1 : E * (M - 1) * F * (E * (M' - 1) * F) = E * ((M - 1) * (M' - 1)) * F := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F E, hFE, Matrix.one_mul]
  have h2 : M * M' - 1 = (M - 1) + (M' - 1) + (M - 1) * (M' - 1) := by noncomm_ring
  simp only [suppMat]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one, h1, h2, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

@[expose] def suppHom [Fintype ι] (hFE : F * E = 1) : Matrix κ κ K →* Matrix ι ι K where
  toFun := suppMat E F
  map_one' := suppMat_one
  map_mul' := suppMat_mul hFE

theorem det_suppMat [Fintype ι] (hFE : F * E = 1) (M : Matrix κ κ K) :
    (suppMat E F M).det = M.det := by
  rw [suppMat, Matrix.mul_assoc, det_one_add_mul_comm, Matrix.mul_assoc, hFE, Matrix.mul_one,
    add_sub_cancel]

theorem suppMat_map (φ : K →+* K) (M : Matrix κ κ K) :
    (suppMat E F M).map φ = suppMat (E.map φ) (F.map φ) (M.map φ) := by
  simp only [suppMat, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
    Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem mul_suppMat [Fintype ι] {A : Matrix ι ι K} {E' : Matrix ι κ K} {F' : Matrix κ ι K}
    {D M M' : Matrix κ κ K} (hAE : A * E' = E * D) (hFA : F * A = D * F')
    (hDM : D * M' = M * D) : A * suppMat E' F' M' = suppMat E F M * A := by
  simp only [suppMat]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  congr 1
  calc A * (E' * (M' - 1) * F') = (A * E') * (M' - 1) * F' := by simp only [Matrix.mul_assoc]
    _ = E * (D * (M' - 1)) * F' := by rw [hAE]; simp only [Matrix.mul_assoc]
    _ = E * ((M - 1) * D) * F' := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hDM, Matrix.mul_one, Matrix.one_mul]
    _ = E * (M - 1) * (D * F') := by simp only [Matrix.mul_assoc]
    _ = E * (M - 1) * F * A := by rw [← hFA]; simp only [Matrix.mul_assoc]

theorem eq_smul_one_of_suppMat [Fintype ι] (hFE : F * E = 1) {M : Matrix κ κ K} {c : K}
    (hM : suppMat E F M = c • 1) : M = c • 1 := by
  have h1 : F * suppMat E F M * E = M := by
    simp only [suppMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [hFE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hFE, Matrix.one_mul, Matrix.mul_assoc,
      hFE, Matrix.mul_one]
    abel
  rw [← h1, hM, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hFE]

end Supp

section Isometry

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {E : Matrix ι κ K}

theorem map_map_of_involutive {m n : Type*} {φ : K →+* K} (hφ : ∀ x, φ (φ x) = x)
    (X : Matrix m n K) : (X.map φ).map φ = X := by
  ext i j
  simp [hφ]

theorem suppMat_isometry {φ : K →+* K} (hφ : ∀ x, φ (φ x) = x) {J : Matrix ι ι K}
    (hJ : (J.map φ)ᵀ = J) {Gi : Matrix κ κ K}
    (hGi : Gi * ((E.map φ)ᵀ * J * E) = 1) (hGi' : ((E.map φ)ᵀ * J * E) * Gi = 1)
    {M : Matrix κ κ K}
    (hM : (M.map φ)ᵀ * ((E.map φ)ᵀ * J * E) * M = (E.map φ)ᵀ * J * E) :
    ((suppMat E (Gi * (E.map φ)ᵀ * J) M).map φ)ᵀ * J *
      suppMat E (Gi * (E.map φ)ᵀ * J) M = J := by
  set G := (E.map φ)ᵀ * J * E with hG
  set F := Gi * (E.map φ)ᵀ * J with hF
  have hGh : (G.map φ)ᵀ = G := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul, ← transpose_map,
      map_map_of_involutive hφ, transpose_transpose, hJ, Matrix.mul_assoc]
  have hGih : (Gi.map φ)ᵀ = Gi := by
    have h1 : G * (Gi.map φ)ᵀ = 1 := by
      have h2 := congrArg (fun X => (X.map φ)ᵀ) hGi
      simp only [Matrix.map_mul, transpose_mul, Matrix.map_one _ (map_zero φ) (map_one φ),
        transpose_one] at h2
      rwa [hGh] at h2
    calc (Gi.map φ)ᵀ = Gi * G * (Gi.map φ)ᵀ := by rw [hGi, Matrix.one_mul]
      _ = Gi := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hFb : (F.map φ)ᵀ = J * E * Gi := by
    rw [hF, Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul, hJ, hGih,
      transpose_map, map_map_of_involutive hφ, transpose_transpose, Matrix.mul_assoc]
  have hGiG : ∀ X : Matrix κ ι K, Gi * (G * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hEJ : (E.map φ)ᵀ * J = G * F := by
    rw [hF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi', Matrix.one_mul]
  have hEJE : ∀ X : Matrix κ ι K, (E.map φ)ᵀ * (J * (E * X)) = G * X := fun X => by
    rw [hG]
    simp only [Matrix.mul_assoc]
  have hbar : ((suppMat E F M).map φ)ᵀ =
      1 + J * E * Gi * ((M.map φ)ᵀ - 1) * (E.map φ)ᵀ := by
    rw [suppMat_map, suppMat, transpose_add, transpose_one, transpose_mul, transpose_mul, hFb,
      transpose_sub, transpose_one]
    simp only [Matrix.mul_assoc]
  rw [hbar]
  calc (1 + J * E * Gi * ((M.map φ)ᵀ - 1) * (E.map φ)ᵀ) * J * suppMat E F M
      = J + J * E * Gi * ((M.map φ)ᵀ * G * M - G) * F := by
        simp only [suppMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
        simp only [hEJE, hEJ, hGiG]
        abel
    _ = J := by rw [hM, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

omit [DecidableEq ι] in
theorem suppF_mul_of_isometry {φ : K →+* K} {J A : Matrix ι ι K} {Gi D : Matrix κ κ K}
    (hA : (A.map φ)ᵀ * J * A = J) (hAE : A * E = E * D)
    (hGi : Gi * ((E.map φ)ᵀ * J * E) = 1) (hGi' : ((E.map φ)ᵀ * J * E) * Gi = 1) :
    Gi * (E.map φ)ᵀ * J * A = D * (Gi * (E.map φ)ᵀ * J) := by
  set G := (E.map φ)ᵀ * J * E with hG
  have hDE : (D.map φ)ᵀ * (E.map φ)ᵀ = (E.map φ)ᵀ * (A.map φ)ᵀ := by
    rw [← transpose_mul, ← transpose_mul, ← Matrix.map_mul, ← Matrix.map_mul, hAE]
  have hD : (D.map φ)ᵀ * G * D = G := by
    calc (D.map φ)ᵀ * G * D = (D.map φ)ᵀ * (E.map φ)ᵀ * J * (E * D) := by
          rw [hG]
          simp only [Matrix.mul_assoc]
      _ = (E.map φ)ᵀ * ((A.map φ)ᵀ * J * A) * E := by
          rw [hDE, ← hAE]
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hA]
  have hX : (D.map φ)ᵀ * ((E.map φ)ᵀ * J * A) = (E.map φ)ᵀ * J := by
    calc (D.map φ)ᵀ * ((E.map φ)ᵀ * J * A) = (D.map φ)ᵀ * (E.map φ)ᵀ * J * A := by
          simp only [Matrix.mul_assoc]
      _ = (E.map φ)ᵀ * ((A.map φ)ᵀ * J * A) := by
          rw [hDE]
          simp only [Matrix.mul_assoc]
      _ = (E.map φ)ᵀ * J := by rw [hA]
  have hinv : (G * D * Gi) * (D.map φ)ᵀ = 1 := by
    refine (mul_eq_one_comm_of_card_eq κ κ K rfl).mp ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hD, hGi']
  calc Gi * (E.map φ)ᵀ * J * A = Gi * ((G * D * Gi) * (D.map φ)ᵀ * ((E.map φ)ᵀ * J * A)) := by
        rw [hinv, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = Gi * G * D * (Gi * (E.map φ)ᵀ * J) := by
        rw [Matrix.mul_assoc (G * D * Gi), hX]
        simp only [Matrix.mul_assoc]
    _ = D * (Gi * (E.map φ)ᵀ * J) := by rw [hGi, Matrix.one_mul]

theorem suppF_mul_of_semilinear {φ : K →+* K} (hφ : ∀ x, φ (φ x) = x) {J A : Matrix ι ι K}
    {Gi D : Matrix κ κ K} {c : K} (hc : c ≠ 0) (hJr : J.map φ = J)
    (hA : (A.map φ)ᵀ * J * A = J) (hAA : A * A.map φ = c • 1) (hAE : A * E.map φ = E * D)
    (hD : Dᵀ * ((E.map φ)ᵀ * J * E).map φ = c • (((E.map φ)ᵀ * J * E) * D))
    (hGi : Gi * ((E.map φ)ᵀ * J * E) = 1) (hGi' : ((E.map φ)ᵀ * J * E) * Gi = 1) :
    Gi * (E.map φ)ᵀ * J * A = D * (Gi * (E.map φ)ᵀ * J).map φ := by
  set G := (E.map φ)ᵀ * J * E with hG
  clear_value G
  have hAA' : A.map φ * A = c • 1 := by
    have h1 : A * (c⁻¹ • A.map φ) = 1 := by
      rw [Matrix.mul_smul, hAA, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 := (mul_eq_one_comm_of_card_eq ι ι K rfl).mp h1
    rw [Matrix.smul_mul] at h2
    calc A.map φ * A = c • (c⁻¹ • (A.map φ * A)) := by
          rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      _ = c • 1 := by rw [h2]
  have hJA : c • (J * A) = Aᵀ * J := by
    calc c • (J * A) = Aᵀ * (A.map φ)ᵀ * J * A := by
          rw [← transpose_mul, hAA', transpose_smul, transpose_one, Matrix.smul_mul,
            Matrix.smul_mul, Matrix.one_mul]
      _ = Aᵀ * J := by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ J, hA]
  have hGGi : G.map φ * Gi.map φ = 1 := by
    rw [← Matrix.map_mul, hGi', Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hFb : G.map φ * (Gi * (E.map φ)ᵀ * J).map φ = Eᵀ * J := by
    have h3 : ((E.map φ)ᵀ).map φ = Eᵀ := by rw [transpose_map, map_map_of_involutive hφ]
    calc G.map φ * (Gi * (E.map φ)ᵀ * J).map φ =
          (G.map φ * Gi.map φ) * ((E.map φ)ᵀ).map φ * J.map φ := by
          rw [Matrix.map_mul, Matrix.map_mul]
          simp only [Matrix.mul_assoc]
      _ = Eᵀ * J := by rw [hGGi, h3, hJr, Matrix.one_mul]
  have hX : c • ((E.map φ)ᵀ * J * A) = c • (G * D * (Gi * (E.map φ)ᵀ * J).map φ) := by
    calc c • ((E.map φ)ᵀ * J * A) = (E.map φ)ᵀ * (c • (J * A)) := by
          rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (A * E.map φ)ᵀ * J := by rw [hJA, transpose_mul, Matrix.mul_assoc]
      _ = Dᵀ * (G.map φ * (Gi * (E.map φ)ᵀ * J).map φ) := by
          rw [hAE, transpose_mul, hFb, Matrix.mul_assoc]
      _ = c • (G * D * (Gi * (E.map φ)ᵀ * J).map φ) := by
          rw [← Matrix.mul_assoc, hD, Matrix.smul_mul]
  have hX' := smul_right_injective _ hc hX
  calc Gi * (E.map φ)ᵀ * J * A = Gi * ((E.map φ)ᵀ * J * A) := by simp only [Matrix.mul_assoc]
    _ = Gi * G * D * (Gi * (E.map φ)ᵀ * J).map φ := by
        rw [hX']
        simp only [Matrix.mul_assoc]
    _ = D * (Gi * (E.map φ)ᵀ * J).map φ := by rw [hGi, Matrix.one_mul]

end Isometry

section Columns

variable {ι κ : Type*}

@[expose] def colMat (v : κ → ι → K) : Matrix ι κ K :=
  Matrix.of fun a i => v i a

theorem map_colMat (φ : K →+* K) (v : κ → ι → K) :
    (colMat v).map φ = colMat fun i a => φ (v i a) :=
  rfl

theorem mul_colMat [Fintype ι] (A : Matrix ι ι K) (v : κ → ι → K) :
    A * colMat v = colMat fun i => A *ᵥ v i := by
  ext a i
  simp [colMat, mul_apply, mulVec, dotProduct]

theorem colMat_mul_smul_one [Fintype κ] [DecidableEq κ] (v : κ → ι → K) (d : K) :
    colMat v * (d • 1 : Matrix κ κ K) = colMat fun i => d • v i := by
  ext a i
  simp [colMat]

theorem gram_colMat [Fintype ι] (φ : K →+* K) (J : Matrix ι ι K) (v : κ → ι → K) :
    ((colMat v).map φ)ᵀ * J * colMat v =
      Matrix.of fun i j => (fun a => φ (v i a)) ⬝ᵥ (J *ᵥ v j) := by
  ext i j
  simp only [colMat, mul_apply, transpose_apply, map_apply, of_apply, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

end Columns

end CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
