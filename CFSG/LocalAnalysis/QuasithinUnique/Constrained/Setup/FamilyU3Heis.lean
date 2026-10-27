module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.LieType.Universal.Unitary

section Heis

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def heisMat (a c : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, c; 0, 1, -σ a; 0, 0, 1]

theorem det_heisMat (a c : K) : (heisMat σ a c).det = 1 := by
  simp [heisMat, Matrix.det_fin_three]

theorem heisMat_mul (a c a' c' : K) :
    heisMat σ a c * heisMat σ a' c' = heisMat σ (a + a') (c + c' - a * σ a') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[expose] noncomputable def heisGL (a c : K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mk'' (heisMat σ a c) (by rw [det_heisMat]; exact isUnit_one)

theorem coe_heisGL (a c : K) :
    ((heisGL σ a c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisMat σ a c :=
  rfl

theorem heisGL_mul (a c a' c' : K) :
    heisGL σ a c * heisGL σ a' c' = heisGL σ (a + a') (c + c' - a * σ a') :=
  Units.ext (by rw [Units.val_mul, coe_heisGL, coe_heisGL, coe_heisGL, heisMat_mul])

theorem antidiag_three' :
    (antidiag 3 : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag]

theorem heisGL_mem_SU (hσ : ∀ x, σ (σ x) = x) {a c : K} (h : c + σ c + a * σ a = 0) :
    heisGL σ a c ∈ SU σ 3 := by
  refine ⟨det_heisMat σ a c, ?_⟩
  rw [coe_heisGL, antidiag_three']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisMat, conjTr, Matrix.mul_apply, Fin.sum_univ_three, hσ]
  linear_combination h

@[expose] def torMat (d : K) : Matrix (Fin 3) (Fin 3) K := !![d, 0, 0; 0, 1, 0; 0, 0, d⁻¹]

theorem det_torMat {d : K} (hd : d ≠ 0) : (torMat d).det = 1 := by
  simp [torMat, Matrix.det_fin_three, hd]

@[expose] noncomputable def torGL {d : K} (hd : d ≠ 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mk'' (torMat d) (by rw [det_torMat hd]; exact isUnit_one)

theorem coe_torGL {d : K} (hd : d ≠ 0) :
    ((torGL hd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = torMat d :=
  rfl

theorem torGL_mem_SU {d : K} (hd : d ≠ 0) (hdσ : σ d = d) : torGL hd ∈ SU σ 3 := by
  refine ⟨det_torMat hd, ?_⟩
  rw [coe_torGL, antidiag_three']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torMat, conjTr, Matrix.mul_apply, Fin.sum_univ_three, hdσ, hd]

theorem torGL_mul_heisGL {d : K} (hd : d ≠ 0) (hdσ : σ d = d) (a c : K) :
    torGL hd * heisGL σ a c = heisGL σ (d * a) (d ^ 2 * c) * torGL hd := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_torGL, coe_heisGL, coe_heisGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torMat, heisMat, Matrix.mul_apply, Fin.sum_univ_three, hdσ] <;> field_simp

theorem torGL_neg_one_mul_self :
    torGL (neg_ne_zero.2 (one_ne_zero : (1 : K) ≠ 0)) *
      torGL (neg_ne_zero.2 (one_ne_zero : (1 : K) ≠ 0)) = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_torGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torMat, Matrix.mul_apply, Fin.sum_univ_three]

section Param

variable {K : Type} [Field K] (σ : K ≃+* K) {F : Type} [Field F] (ι : F →+* K) (ω : K)

@[expose] noncomputable def vH (x y : F) : GL (Fin 3) K :=
  heisGL σ (ι x) (-(ι x) ^ 2 / 2 + ι y * ω)

@[expose] noncomputable def shearGL (κ : F) : GL (Fin 3) K :=
  heisGL σ (-(ι κ) * ω / 2) ((ι κ) ^ 2 * ω ^ 2 / 8)

variable {σ ι ω}

theorem vH_mem (h2 : (2 : K) ≠ 0) (hσ : ∀ x, σ (σ x) = x) (hι : ∀ x, σ (ι x) = ι x)
    (hω : σ ω = -ω) (x y : F) : vH σ ι ω x y ∈ SU σ 3 := by
  apply heisGL_mem_SU σ hσ
  have h2' : σ (2 : K) = 2 := map_ofNat σ 2
  simp only [map_add, map_mul, map_div₀, map_neg, map_pow, h2', hι, hω]
  field_simp
  ring

theorem vH_mul (h2 : (2 : K) ≠ 0) (hι : ∀ x, σ (ι x) = ι x) (x y x' y' : F) :
    vH σ ι ω x y * vH σ ι ω x' y' = vH σ ι ω (x + x') (y + y') := by
  unfold vH
  rw [heisGL_mul, hι]
  congr 1
  · rw [map_add]
  · simp only [map_add]
    field_simp
    ring

theorem heisGL_zero : heisGL σ (0 : K) 0 = 1 := by
  apply Units.ext
  rw [coe_heisGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisMat]

theorem vH_zero : vH σ ι ω 0 0 = 1 := by
  unfold vH
  simp [heisGL_zero]

theorem torGL_mul_vH {d : K} (hd : d ≠ 0) (hdσ : σ d = d) (x y : F) (x' y' : F)
    (hx : ι x' = d * ι x) (hy : ι y' = d ^ 2 * ι y) :
    torGL hd * vH σ ι ω x y = vH σ ι ω x' y' * torGL hd := by
  unfold vH
  rw [torGL_mul_heisGL σ hd hdσ, hx, hy]
  congr 2
  ring

theorem shearGL_mem (h2 : (2 : K) ≠ 0) (hσ : ∀ x, σ (σ x) = x) (hι : ∀ x, σ (ι x) = ι x)
    (hω : σ ω = -ω) (κ : F) : shearGL σ ι ω κ ∈ SU σ 3 := by
  apply heisGL_mem_SU σ hσ
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 ^ 3 := by norm_num
    rw [this]
    exact pow_ne_zero 3 h2
  have h2' : σ (2 : K) = 2 := map_ofNat σ 2
  have h8' : σ (8 : K) = 8 := map_ofNat σ 8
  simp only [map_mul, map_div₀, map_neg, map_pow, h2', h8', hι, hω]
  field_simp
  ring

theorem shearGL_mul_vH (h2 : (2 : K) ≠ 0) (hι : ∀ x, σ (ι x) = ι x) (hω : σ ω = -ω) (κ x y : F) :
    shearGL σ ι ω κ * vH σ ι ω x y = vH σ ι ω x (y + κ * x) * shearGL σ ι ω κ := by
  unfold vH shearGL
  rw [heisGL_mul, heisGL_mul, hι]
  have h2' : σ (2 : K) = 2 := map_ofNat σ 2
  congr 1
  · ring
  · simp only [map_add, map_mul, map_div₀, map_neg, h2', hι, hω]
    field_simp
    ring

theorem vH_not_scalar {x y : F} (hω0 : ω ≠ 0) {r : Kˣ}
    (h : vH σ ι ω x y = GeneralLinearGroup.scalar (Fin 3) r) : x = 0 ∧ y = 0 := by
  have e1 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 1) h
  have e2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 2) h
  simp only [vH, coe_heisGL, heisMat, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply] at e1 e2
  have hx : x = 0 := by simpa using e1
  subst hx
  refine ⟨rfl, ?_⟩
  have e2' : ι y * ω = 0 := by simpa using e2
  exact ι.injective (by rw [map_zero]; exact (mul_eq_zero.1 e2').resolve_right hω0)

end Param

end Heis

end CFSG.QuasithinUnique.Setup.Family
