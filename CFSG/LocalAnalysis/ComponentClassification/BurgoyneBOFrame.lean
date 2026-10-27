module

public import CFSG.LieType.HighestRoot.CentSpinBasic
public import CFSG.LieType.HighestRoot.Defs

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.Universal.Spin CFSG.LieType.HighestRoot CliffordAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def dGL (ν : Kˣ) : GL (Fin 2) K :=
  ⟨!![1, 0; 0, (ν : K)], !![1, 0; 0, ((ν⁻¹ : Kˣ) : K)], by
    ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem coe_dGL (ν : Kˣ) : ((dGL ν : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 0; 0, (ν : K)] := rfl

theorem coe_dGL_inv (ν : Kˣ) : (((dGL ν)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 0; 0, ((ν⁻¹ : Kˣ) : K)] := rfl

@[expose] def conjSL₂ (D : GL (Fin 2) K) (A : SL(2, K)) : SL(2, K) :=
  ⟨(D : Matrix (Fin 2) (Fin 2) K) * A * ((D⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem coe_conjSL₂ (D : GL (Fin 2) K) (A : SL(2, K)) :
    ((conjSL₂ D A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (D : Matrix (Fin 2) (Fin 2) K) * A * ((D⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

section Similitude

variable {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} {T : V ≃ₗ[K] V'} {ν : Kˣ}

theorem polar_similitude (hT : ∀ v, Q' (T v) = ν * Q v) (x y : V) :
    polar Q' (T x) (T y) = ν * polar Q x y := by
  simp only [polar, ← map_add, hT]
  ring

theorem Q_symm (hT : ∀ v, Q' (T v) = ν * Q v) (x : V') :
    Q (T.symm x) = (ν⁻¹ : Kˣ) * Q' x := by
  rw [← T.apply_symm_apply x, hT, T.symm_apply_apply, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul]

theorem polar_symm (hT : ∀ v, Q' (T v) = ν * Q v) (x y : V') :
    polar Q (T.symm x) (T.symm y) = (ν⁻¹ : Kˣ) * polar Q' x y := by
  rw [← T.apply_symm_apply x, ← T.apply_symm_apply y, polar_similitude hT, T.symm_apply_apply,
    T.symm_apply_apply, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

@[expose] def frameComap (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v) : Frame Q where
  P := ⟨T.symm F.e₁, (ν : K) • T.symm F.f₁, by rw [Q_symm hT, F.Q_e₁, mul_zero], by
    rw [map_smul_eq_sq, Q_symm hT, F.Q_f₁, mul_zero, mul_zero], by
    rw [polar_smul_right, polar_symm hT, F.polar_e₁_f₁, mul_one, smul_eq_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]⟩
  P' := ⟨T.symm F.e₂, (ν : K) • T.symm F.f₂, by rw [Q_symm hT, F.Q_e₂, mul_zero], by
    rw [map_smul_eq_sq, Q_symm hT, F.Q_f₂, mul_zero, mul_zero], by
    rw [polar_smul_right, polar_symm hT, F.polar_e₂_f₂, mul_one, smul_eq_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]⟩
  orth :=
    ⟨by rw [polar_symm hT, F.polar_e₁_e₂, mul_zero],
      by rw [polar_smul_right, polar_symm hT, F.polar_e₁_f₂, mul_zero, smul_zero],
      by rw [polar_smul_left, polar_symm hT, F.polar_f₁_e₂, mul_zero, smul_zero],
      by rw [polar_smul_left, polar_smul_right, polar_symm hT, F.polar_f₁_f₂, mul_zero,
        smul_zero, smul_zero]⟩

theorem frameComap_e₁ (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v) :
    (frameComap F hT).e₁ = T.symm F.e₁ := rfl

theorem frameComap_f₁ (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v) :
    (frameComap F hT).f₁ = (ν : K) • T.symm F.f₁ := rfl

theorem frameComap_e₂ (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v) :
    (frameComap F hT).e₂ = T.symm F.e₂ := rfl

theorem frameComap_f₂ (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v) :
    (frameComap F hT).f₂ = (ν : K) • T.symm F.f₂ := rfl

theorem frameComap_coords (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v) (v : V) :
    (frameComap F hT).coords v =
      (((dGL ν)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * F.coords (T v) := by
  have h : ∀ y : V', polar Q v (T.symm y) = (ν⁻¹ : Kˣ) * polar Q' (T v) y := by
    intro y
    rw [← polar_symm hT, T.symm_apply_apply]
  rw [Frame.coords_apply, Frame.coords_apply, coe_dGL_inv, frameComap_e₁, frameComap_f₁,
    frameComap_e₂, frameComap_f₂, polar_smul_right, polar_smul_right, h, h, h, h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

theorem frameComap_incl (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (frameComap F hT).incl X = T.symm (F.incl ((dGL ν : Matrix (Fin 2) (Fin 2) K) * X)) := by
  rw [Frame.incl_apply, Frame.incl_apply, coe_dGL, frameComap_e₁, frameComap_f₁, frameComap_e₂,
    frameComap_f₂]
  simp [Matrix.mul_apply, Fin.sum_univ_two, smul_smul, mul_comm]

theorem frameComap_La (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v) (A : SL(2, K)) (v : V) :
    (frameComap F hT).La A v = T.symm (F.La (conjSL₂ (dGL ν) A) (T v)) := by
  rw [Frame.La_apply, Frame.La_apply, frameComap_coords, frameComap_incl, map_add,
    T.symm_apply_apply, coe_conjSL₂]
  congr 2
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_assoc]

theorem frameComap_swap_La (F : Frame Q') (hT : ∀ v, Q' (T v) = ν * Q v) (A : SL(2, K))
    (v : V) : (frameComap F hT).swap.La A v = T.symm (F.swap.La A (T v)) := by
  rw [Frame.La_swap_apply, Frame.La_swap_apply, Frame.embLin_apply, Frame.embLin_apply,
    frameComap_coords, frameComap_incl, map_add, T.symm_apply_apply]
  congr 2
  simp only [LinearMap.mulRight_apply]
  have hDc : (dGL ν : Matrix (Fin 2) (Fin 2) K) * ((((dGL ν)⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) * F.coords (T v)) = F.coords (T v) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hDc]

end Similitude

section Hyp

variable {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def frameVec (F : Frame Q) : Fin 2 → Bool → V
  | ⟨0, _⟩, true => F.e₁
  | ⟨0, _⟩, false => F.f₁
  | ⟨1, _⟩, true => F.e₂
  | ⟨1, _⟩, false => F.f₂

@[expose] def frameHyp (F : Frame Q) (a : V) (ha : IsUnit (Q a))
    (hperp : polar Q F.e₁ a = 0 ∧ polar Q F.f₁ a = 0 ∧ polar Q F.e₂ a = 0 ∧
      polar Q F.f₂ a = 0) : HypFrame Q 2 where
  vec := frameVec F
  map_vec i s := by
    fin_cases i <;> cases s <;> simp [frameVec, F.Q_e₁, F.Q_f₁, F.Q_e₂, F.Q_f₂]
  polar_vec_of_ne i j hij s t := by
    fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
      simp_all [frameVec, F.polar_e₁_e₂, F.polar_e₁_f₂, F.polar_f₁_e₂, F.polar_f₁_f₂,
        F.polar_e₂_e₁, F.polar_f₂_e₁, F.polar_e₂_f₁, F.polar_f₂_f₁]
  polar_vec_not i s := by
    fin_cases i <;> cases s <;>
      simp [frameVec, F.polar_e₁_f₁, F.polar_f₁_e₁, F.polar_e₂_f₂, F.polar_f₂_e₂]
  exists_aux i j := ⟨a, ha, fun s => by
    obtain ⟨h1, h2, h3, h4⟩ := hperp
    fin_cases i <;> fin_cases j <;> cases s <;> simp [frameVec, h1, h2, h3, h4]⟩

theorem frameHyp_toFrame (F : Frame Q) (a : V) (ha : IsUnit (Q a))
    (hperp : polar Q F.e₁ a = 0 ∧ polar Q F.f₁ a = 0 ∧ polar Q F.e₂ a = 0 ∧
      polar Q F.f₂ a = 0) :
    (frameHyp F a ha hperp).toFrame (show (0 : Fin 2) ≠ 1 by decide) true true = F := by
  rcases F with ⟨⟨e₁, f₁, _, _, _⟩, ⟨e₂, f₂, _, _, _⟩, _⟩
  rfl

theorem spinAction_frameHyp_longSL2 (F : Frame Q) (a : V) (ha : IsUnit (Q a))
    (hperp : polar Q F.e₁ a = 0 ∧ polar Q F.f₁ a = 0 ∧ polar Q F.e₂ a = 0 ∧
      polar Q F.f₂ a = 0) (A : SL(2, K)) :
    spinAction Q ((frameHyp F a ha hperp).longSL2 (show (0 : Fin 2) ≠ 1 by decide) true true A) =
      F.La A := by
  rw [spinAction_longSL2, frameHyp_toFrame]

theorem spinAction_frameHyp_longSL2_swap (F : Frame Q) (a : V) (ha : IsUnit (Q a))
    (hperp : polar Q F.e₁ a = 0 ∧ polar Q F.f₁ a = 0 ∧ polar Q F.e₂ a = 0 ∧
      polar Q F.f₂ a = 0) (A : SL(2, K)) :
    spinAction Q ((frameHyp F a ha hperp).longSL2 (show (0 : Fin 2) ≠ 1 by decide) true false A) =
      F.swap.La A := by
  rw [spinAction_longSL2, show false = !true from rfl, toFrame_not, frameHyp_toFrame]

theorem frameHyp_longSL2_neg_one_mul (F : Frame Q) (a : V) (ha : IsUnit (Q a))
    (hperp : polar Q F.e₁ a = 0 ∧ polar Q F.f₁ a = 0 ∧ polar Q F.e₂ a = 0 ∧
      polar Q F.f₂ a = 0) :
    (((frameHyp F a ha hperp).longSL2 (show (0 : Fin 2) ≠ 1 by decide) true true (-1) *
      (frameHyp F a ha hperp).longSL2 (show (0 : Fin 2) ≠ 1 by decide) true false (-1) :
        spinGroup Q) : CliffordAlgebra Q) = -1 := by
  have h := coe_longSL2_not_neg_one (frameHyp F a ha hperp) (show (0 : Fin 2) ≠ 1 by decide)
    true true
  simp only [Bool.not_true] at h
  rw [Submonoid.coe_mul, h, mul_neg, ← Submonoid.coe_mul, ← map_mul,
    show (-1 : SL(2, K)) * -1 = 1 by simp, map_one, Submonoid.coe_one]

end Hyp

end CFSG.ComponentClassification.Burgoyne.B
