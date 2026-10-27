module

public import CFSG.Open.StatedDefs
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import Mathlib.RingTheory.Frobenius
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open Matrix

variable {F : Type} [Field F] [DecidableEq F]

@[expose] def eigP (d : Fin 6 → F) (l : F) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.diagonal fun i => if d i = l then 1 else 0

@[expose] def blkM (d : Fin 6 → F) (l : F) (h : Matrix (Fin 6) (Fin 6) F) : Matrix (Fin 6) (Fin 6) F :=
  eigP d l * h * eigP d l + (1 - eigP d l)

theorem eigP_mul_same (d : Fin 6 → F) (l : F) : eigP d l * eigP d l = eigP d l := by
  unfold eigP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem eigP_mul_ne (d : Fin 6 → F) {l m : F} (h : l ≠ m) : eigP d l * eigP d m = 0 := by
  unfold eigP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext i
  split_ifs with h1 h2 <;> simp_all

theorem eigP_mul_one_sub (d : Fin 6 → F) (l : F) : eigP d l * (1 - eigP d l) = 0 := by
  rw [mul_sub, eigP_mul_same, mul_one, sub_self]

theorem one_sub_mul_eigP (d : Fin 6 → F) (l : F) : (1 - eigP d l) * eigP d l = 0 := by
  rw [sub_mul, one_mul, eigP_mul_same, sub_self]

theorem one_sub_mul_one_sub (d : Fin 6 → F) (l : F) :
    (1 - eigP d l) * (1 - eigP d l) = 1 - eigP d l := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, eigP_mul_same]
  abel

theorem eigP_transpose (d : Fin 6 → F) (l : F) : (eigP d l)ᵀ = eigP d l := by
  unfold eigP
  rw [Matrix.diagonal_transpose]

theorem eigP_map (d : Fin 6 → F) (l : F) :
    (eigP d l).map (fun x : F => x ^ 2 ^ 2) = eigP d l := by
  ext i j
  unfold eigP
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.map_apply]
    split_ifs <;> simp
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem blkM_of_comm (d : Fin 6 → F) (l : F) {h : Matrix (Fin 6) (Fin 6) F}
    (hh : h * eigP d l = eigP d l * h) :
    blkM d l h = h * eigP d l + (1 - eigP d l) := by
  unfold blkM
  rw [← hh, mul_assoc, eigP_mul_same]

theorem blkM_mul (d : Fin 6 → F) (l : F) {h k : Matrix (Fin 6) (Fin 6) F}
    (hh : h * eigP d l = eigP d l * h) (hk : k * eigP d l = eigP d l * k) :
    blkM d l (h * k) = blkM d l h * blkM d l k := by
  have hhk : (h * k) * eigP d l = eigP d l * (h * k) := by
    calc h * k * eigP d l = h * (k * eigP d l) := mul_assoc _ _ _
      _ = h * (eigP d l * k) := by rw [hk]
      _ = (h * eigP d l) * k := (mul_assoc _ _ _).symm
      _ = (eigP d l * h) * k := by rw [hh]
      _ = eigP d l * (h * k) := mul_assoc _ _ _
  have e1 : h * eigP d l * (k * eigP d l) = h * k * eigP d l := by
    calc h * eigP d l * (k * eigP d l) = h * (eigP d l * k) * eigP d l := by simp only [mul_assoc]
      _ = h * (k * eigP d l) * eigP d l := by rw [← hk]
      _ = h * k * eigP d l := by simp only [mul_assoc, eigP_mul_same]
  have e2 : h * eigP d l * (1 - eigP d l) = 0 := by
    rw [mul_assoc, eigP_mul_one_sub, mul_zero]
  have hQk : (1 - eigP d l) * k = k * (1 - eigP d l) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hk]
  have e3 : (1 - eigP d l) * (k * eigP d l) = 0 := by
    rw [← mul_assoc, hQk, mul_assoc, one_sub_mul_eigP, mul_zero]
  rw [blkM_of_comm d l hhk, blkM_of_comm d l hh, blkM_of_comm d l hk]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, one_sub_mul_one_sub]
  simp

theorem blkM_one (d : Fin 6 → F) (l : F) : blkM d l 1 = 1 := by
  unfold blkM
  rw [mul_one, eigP_mul_same]
  abel

theorem blkM_eq_self (d : Fin 6 → F) (l : F) {u : Matrix (Fin 6) (Fin 6) F}
    (hu : u * eigP d l = eigP d l * u) (hQ : u * (1 - eigP d l) = 1 - eigP d l) :
    blkM d l u = u := by
  rw [blkM_of_comm d l hu, ← hQ, ← mul_add, add_sub_cancel, mul_one]

theorem blkM_eq_one (d : Fin 6 → F) {l m : F} (hne : l ≠ m) {u : Matrix (Fin 6) (Fin 6) F}
    (hu : u * eigP d l = eigP d l * u) (hum : u * (1 - eigP d m) = 1 - eigP d m) :
    blkM d l u = 1 := by
  have h1 : (1 - eigP d m) * eigP d l = eigP d l := by
    rw [sub_mul, one_mul, eigP_mul_ne d (Ne.symm hne), sub_zero]
  have h2 : u * eigP d l = eigP d l := by
    rw [← h1, ← mul_assoc, hum]
  rw [blkM_of_comm d l hu, h2, add_sub_cancel]

theorem blkM_comm_eigP (d : Fin 6 → F) (l : F) {x : Matrix (Fin 6) (Fin 6) F}
    (hx : ∀ m, x * eigP d m = eigP d m * x) (m : F) :
    blkM d l x * eigP d m = eigP d m * blkM d l x := by
  rw [blkM_of_comm d l (hx l)]
  by_cases hlm : l = m
  · subst hlm
    have L : (x * eigP d l + (1 - eigP d l)) * eigP d l = x * eigP d l := by
      rw [add_mul, mul_assoc, eigP_mul_same, one_sub_mul_eigP, add_zero]
    have R : eigP d l * (x * eigP d l + (1 - eigP d l)) = x * eigP d l := by
      rw [mul_add, ← mul_assoc, ← hx l, mul_assoc, eigP_mul_same, eigP_mul_one_sub, add_zero]
    rw [L, R]
  · have hml : eigP d m * eigP d l = 0 := eigP_mul_ne d (Ne.symm hlm)
    have hlm' : eigP d l * eigP d m = 0 := eigP_mul_ne d hlm
    have L : (x * eigP d l + (1 - eigP d l)) * eigP d m = eigP d m := by
      rw [add_mul, mul_assoc, hlm', mul_zero, zero_add, sub_mul, one_mul, hlm', sub_zero]
    have R : eigP d m * (x * eigP d l + (1 - eigP d l)) = eigP d m := by
      rw [mul_add, ← mul_assoc, ← hx m, mul_assoc, hml, mul_zero, zero_add, mul_sub, mul_one, hml,
        sub_zero]
    rw [L, R]

theorem blkM_unitary (d : Fin 6 → F) (l : F) [CharP F 2] {x : Matrix (Fin 6) (Fin 6) F}
    (hx : x * eigP d l = eigP d l * x)
    (hU : ((x.map (iterateFrobenius F 2 2 : F →+* F)))ᵀ * x = 1) :
    ((blkM d l x).map (iterateFrobenius F 2 2 : F →+* F))ᵀ * blkM d l x = 1 := by
  set φ : F →+* F := iterateFrobenius F 2 2 with hφdef
  have hφeq : (⇑φ) = fun y : F => y ^ 2 ^ 2 := by
    funext a
    rfl
  have hPφ : (eigP d l).map φ = eigP d l := by
    rw [hφeq]
    exact eigP_map d l
  have hXφ : (x.map φ) * eigP d l = eigP d l * (x.map φ) := by
    have := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M.map φ) hx
    simpa only [Matrix.map_mul, hPφ] using this
  have hAP : eigP d l * (x.map φ)ᵀ = (x.map φ)ᵀ * eigP d l := by
    have := congrArg Matrix.transpose hXφ
    simpa only [Matrix.transpose_mul, eigP_transpose] using this
  have hY : (blkM d l x).map φ = eigP d l * (x.map φ) * eigP d l + (1 - eigP d l) := by
    unfold blkM
    rw [Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
      Matrix.map_one _ (map_zero φ) (map_one φ), hPφ]
  have hYt : ((blkM d l x).map φ)ᵀ = eigP d l * (x.map φ)ᵀ * eigP d l + (1 - eigP d l) := by
    rw [hY]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, eigP_transpose, mul_assoc]
  have t1 : eigP d l * (x.map φ)ᵀ * eigP d l * (eigP d l * x * eigP d l) = eigP d l := by
    calc eigP d l * (x.map φ)ᵀ * eigP d l * (eigP d l * x * eigP d l)
        = eigP d l * (x.map φ)ᵀ * (eigP d l * eigP d l) * x * eigP d l := by simp only [mul_assoc]
      _ = eigP d l * (x.map φ)ᵀ * eigP d l * x * eigP d l := by rw [eigP_mul_same]
      _ = eigP d l * ((x.map φ)ᵀ * eigP d l) * x * eigP d l := by simp only [mul_assoc]
      _ = eigP d l * (eigP d l * (x.map φ)ᵀ) * x * eigP d l := by rw [← hAP]
      _ = eigP d l * (eigP d l * ((x.map φ)ᵀ * x)) * eigP d l := by simp only [mul_assoc]
      _ = eigP d l * (eigP d l * 1) * eigP d l := by rw [hU]
      _ = eigP d l := by simp only [mul_one, eigP_mul_same]
  have t2 : eigP d l * (x.map φ)ᵀ * eigP d l * (1 - eigP d l) = 0 := by
    calc eigP d l * (x.map φ)ᵀ * eigP d l * (1 - eigP d l)
        = eigP d l * (x.map φ)ᵀ * (eigP d l * (1 - eigP d l)) := by simp only [mul_assoc]
      _ = 0 := by rw [eigP_mul_one_sub, mul_zero]
  have t3 : (1 - eigP d l) * (eigP d l * x * eigP d l) = 0 := by
    calc (1 - eigP d l) * (eigP d l * x * eigP d l)
        = ((1 - eigP d l) * eigP d l) * x * eigP d l := by simp only [mul_assoc]
      _ = 0 := by rw [one_sub_mul_eigP]; simp
  rw [hYt]
  unfold blkM
  rw [add_mul, mul_add, mul_add, t1, t2, t3, one_sub_mul_one_sub]
  simp

theorem blkM_mul_one_sub (d : Fin 6 → F) (l : F) (u : Matrix (Fin 6) (Fin 6) F) :
    blkM d l u * (1 - eigP d l) = 1 - eigP d l := by
  unfold blkM
  rw [add_mul, mul_assoc, eigP_mul_one_sub, mul_zero, zero_add, one_sub_mul_one_sub]

theorem eq_one_of_eigP_fix (d : Fin 6 → F) {x : Matrix (Fin 6) (Fin 6) F}
    (h : ∀ k : Fin 6, x * eigP d (d k) = eigP d (d k)) : x = 1 := by
  ext j k
  have h1 := congrFun (congrFun (h k) j) k
  simp only [eigP, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply] at h1 ⊢
  split_ifs at h1 ⊢ <;> simp_all

theorem inv_comm_of (g : GL (Fin 6) F) {M : Matrix (Fin 6) (Fin 6) F}
    (h : (g : Matrix (Fin 6) (Fin 6) F) * M = M * (g : Matrix (Fin 6) (Fin 6) F)) :
    ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * M =
      M * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
  calc ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * M
      = ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * M *
          ((g : Matrix (Fin 6) (Fin 6) F) * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) := by
        rw [Units.mul_inv, mul_one]
    _ = ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (M * (g : Matrix (Fin 6) (Fin 6) F)) *
          ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by simp only [mul_assoc]
    _ = ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * ((g : Matrix (Fin 6) (Fin 6) F) * M) *
          ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by rw [← h]
    _ = M * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
        rw [Units.inv_mul_cancel_left]

end CFSG.LocalAnalysis.GLTheoremA.SFM12
