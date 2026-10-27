module

public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.OrthQ8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_eq_zero_of_mul_self (h2 : (2 : K) ≠ 0) {J : V ≃ₗ[K] V}
    (hJ : J ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {v : V} (h : J (J v) = -v) :
    polar Q v (J v) = 0 := by
  have h1 := polar_map_of_mem hJ v (J v)
  rw [h, polar_neg_right, polar_comm] at h1
  have h3 : (2 : K) * polar Q v (J v) = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h3).resolve_left h2

private theorem two_ne_zero_of (h3 : (3 : K) = 0) : (2 : K) ≠ 0 := fun h2 =>
  one_ne_zero (by linear_combination h3 - h2 : (1 : K) = 0)

structure OrthoQuad (Q : QuadraticForm K V) (w₀ w₁ w₂ w₃ : V) : Prop where
  Q₀ : Q w₀ = 1
  Q₁ : Q w₁ = 1
  Q₂ : Q w₂ = 1
  Q₃ : Q w₃ = 1
  p₀₁ : polar Q w₀ w₁ = 0
  p₀₂ : polar Q w₀ w₂ = 0
  p₀₃ : polar Q w₀ w₃ = 0
  p₁₂ : polar Q w₁ w₂ = 0
  p₁₃ : polar Q w₁ w₃ = 0
  p₂₃ : polar Q w₂ w₃ = 0

@[expose] def comb4 (w₀ w₁ w₂ w₃ : V) (c₀ c₁ c₂ c₃ : K) : V :=
  c₀ • w₀ + c₁ • w₁ + c₂ • w₂ + c₃ • w₃

theorem comb4_congr {w₀ w₁ w₂ w₃ : V} {c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : K} (h₀ : c₀ = d₀)
    (h₁ : c₁ = d₁) (h₂ : c₂ = d₂) (h₃ : c₃ = d₃) :
    comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃ = comb4 w₀ w₁ w₂ w₃ d₀ d₁ d₂ d₃ := by
  rw [h₀, h₁, h₂, h₃]

private theorem sl2IJ_coe (h3 : (3 : K) = 0) :
    ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * ((sl2J h3 : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) = !![1, -1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2I, coe_sl2J, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sl2I_mul_sl2I :
    ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * ((sl2I : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2I, Matrix.mul_apply, Fin.sum_univ_two]

namespace OrthoQuad

variable {w₀ w₁ w₂ w₃ : V} (h : OrthoQuad Q w₀ w₁ w₂ w₃)
include h

theorem polar_comb (c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : K) :
    polar Q (comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃) (comb4 w₀ w₁ w₂ w₃ d₀ d₁ d₂ d₃) =
      2 * (c₀ * d₀ + c₁ * d₁ + c₂ * d₂ + c₃ * d₃) := by
  have s0 : polar Q w₀ w₀ = 2 := by rw [polar_self, h.Q₀]; ring
  have s1 : polar Q w₁ w₁ = 2 := by rw [polar_self, h.Q₁]; ring
  have s2 : polar Q w₂ w₂ = 2 := by rw [polar_self, h.Q₂]; ring
  have s3 : polar Q w₃ w₃ = 2 := by rw [polar_self, h.Q₃]; ring
  have r10 : polar Q w₁ w₀ = 0 := by rw [polar_comm, h.p₀₁]
  have r20 : polar Q w₂ w₀ = 0 := by rw [polar_comm, h.p₀₂]
  have r30 : polar Q w₃ w₀ = 0 := by rw [polar_comm, h.p₀₃]
  have r21 : polar Q w₂ w₁ = 0 := by rw [polar_comm, h.p₁₂]
  have r31 : polar Q w₃ w₁ = 0 := by rw [polar_comm, h.p₁₃]
  have r32 : polar Q w₃ w₂ = 0 := by rw [polar_comm, h.p₂₃]
  simp only [comb4, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    smul_eq_mul, h.p₀₁, h.p₀₂, h.p₀₃, h.p₁₂, h.p₁₃, h.p₂₃, r10, r20, r30, r21, r31, r32, s0, s1,
    s2, s3]
  ring

theorem Q_comb (h2 : (2 : K) ≠ 0) (c₀ c₁ c₂ c₃ : K) :
    Q (comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃) = c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 := by
  have h1 := h.polar_comb c₀ c₁ c₂ c₃ c₀ c₁ c₂ c₃
  rw [polar_self] at h1
  have h4 : (2 : K) * (Q (comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃) -
      (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2)) = 0 := by
    linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h2)

@[expose] def frame (h3 : (3 : K) = 0) : Frame Q where
  P := ⟨comb4 w₀ w₁ w₂ w₃ (-1 : K) 0 1 1, comb4 w₀ w₁ w₂ w₃ (-1 : K) 0 (-1) (-1),
    by rw [h.Q_comb (two_ne_zero_of h3)]; linear_combination h3,
    by rw [h.Q_comb (two_ne_zero_of h3)]; linear_combination h3,
    by rw [h.polar_comb]; linear_combination -h3⟩
  P' := ⟨comb4 w₀ w₁ w₂ w₃ (0 : K) 1 (-1) 1, comb4 w₀ w₁ w₂ w₃ (0 : K) 1 1 (-1),
    by rw [h.Q_comb (two_ne_zero_of h3)]; linear_combination h3,
    by rw [h.Q_comb (two_ne_zero_of h3)]; linear_combination h3,
    by rw [h.polar_comb]; linear_combination -h3⟩
  orth :=
    ⟨show polar Q (comb4 w₀ w₁ w₂ w₃ (-1 : K) 0 1 1) (comb4 w₀ w₁ w₂ w₃ (0 : K) 1 (-1) 1) = 0 by
        rw [h.polar_comb]; ring,
      show polar Q (comb4 w₀ w₁ w₂ w₃ (-1 : K) 0 1 1) (comb4 w₀ w₁ w₂ w₃ (0 : K) 1 1 (-1)) = 0 by
        rw [h.polar_comb]; ring,
      show polar Q (comb4 w₀ w₁ w₂ w₃ (-1 : K) 0 (-1) (-1))
          (comb4 w₀ w₁ w₂ w₃ (0 : K) 1 (-1) 1) = 0 by
        rw [h.polar_comb]; ring,
      show polar Q (comb4 w₀ w₁ w₂ w₃ (-1 : K) 0 (-1) (-1))
          (comb4 w₀ w₁ w₂ w₃ (0 : K) 1 1 (-1)) = 0 by
        rw [h.polar_comb]; ring⟩

theorem incl_frame (h3 : (3 : K) = 0) (M : Matrix (Fin 2) (Fin 2) K) :
    (h.frame h3).incl M = comb4 w₀ w₁ w₂ w₃ (-M 0 0 - M 1 1) (-M 0 1 + M 1 0)
      (M 0 0 - M 1 1 + M 0 1 + M 1 0) (M 0 0 - M 1 1 - M 0 1 - M 1 0) := by
  rw [Frame.incl_apply]
  show M 0 0 • comb4 w₀ w₁ w₂ w₃ (-1 : K) 0 1 1 + M 1 1 • comb4 w₀ w₁ w₂ w₃ (-1 : K) 0 (-1) (-1) +
    (-M 0 1) • comb4 w₀ w₁ w₂ w₃ (0 : K) 1 (-1) 1 + M 1 0 • comb4 w₀ w₁ w₂ w₃ (0 : K) 1 1 (-1) = _
  simp only [comb4]
  module

omit h in
private theorem comb4_eq {c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : K} (h₀ : c₀ = d₀) (h₁ : c₁ = d₁)
    (h₂ : c₂ = d₂) (h₃ : c₃ = d₃) :
    comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃ = d₀ • w₀ + d₁ • w₁ + d₂ • w₂ + d₃ • w₃ := by
  rw [h₀, h₁, h₂, h₃]
  rfl

theorem incl_one (h3 : (3 : K) = 0) : (h.frame h3).incl 1 = w₀ := by
  rw [incl_frame, comb4_eq (d₀ := 1) (d₁ := 0) (d₂ := 0) (d₃ := 0)
    (by simp only [Matrix.one_apply_eq]; linear_combination -h3) (by simp) (by simp) (by simp)]
  simp

theorem incl_sl2I (h3 : (3 : K) = 0) :
    (h.frame h3).incl ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = w₁ := by
  rw [incl_frame, coe_sl2I, comb4_eq (d₀ := 0) (d₁ := 1) (d₂ := 0) (d₃ := 0) (by simp)
    (by simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]; linear_combination -h3) (by simp) (by simp)]
  simp

theorem incl_sl2J (h3 : (3 : K) = 0) :
    (h.frame h3).incl ((sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = w₂ := by
  rw [incl_frame, coe_sl2J, comb4_eq (d₀ := 0) (d₁ := 0) (d₂ := 1) (d₃ := 0) (by simp)
    (by simp)
    (by simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]; linear_combination h3) (by simp)]
  simp

theorem incl_sl2IJ (h3 : (3 : K) = 0) :
    (h.frame h3).incl (((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      ((sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) = w₃ := by
  rw [incl_frame, sl2IJ_coe h3, comb4_eq (d₀ := 0) (d₁ := 0) (d₂ := 0) (d₃ := 1) (by simp)
    (by simp) (by simp)
    (by simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]; linear_combination h3)]
  simp

theorem La_sl2I_w₀ (h3 : (3 : K) = 0) : (h.frame h3).La sl2I w₀ = w₁ := by
  have h1 := Frame.La_apply_incl (h.frame h3) sl2I 1
  rwa [Matrix.mul_one, h.incl_sl2I h3, h.incl_one h3] at h1

theorem La_sl2I_w₁ (h3 : (3 : K) = 0) : (h.frame h3).La sl2I w₁ = -w₀ := by
  have h1 := Frame.La_apply_incl (h.frame h3) sl2I ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  rwa [sl2I_mul_sl2I, map_neg, h.incl_one h3, h.incl_sl2I h3] at h1

theorem La_sl2I_w₂ (h3 : (3 : K) = 0) : (h.frame h3).La sl2I w₂ = w₃ := by
  have h1 := Frame.La_apply_incl (h.frame h3) sl2I ((sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  rwa [h.incl_sl2IJ h3, h.incl_sl2J h3] at h1

theorem La_sl2I_w₃ (h3 : (3 : K) = 0) : (h.frame h3).La sl2I w₃ = -w₂ := by
  have h1 := Frame.La_apply_incl (h.frame h3) sl2I (((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
    ((sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))
  rwa [← Matrix.mul_assoc, sl2I_mul_sl2I, Matrix.neg_mul, Matrix.one_mul, map_neg,
    h.incl_sl2J h3, h.incl_sl2IJ h3] at h1

theorem La_fix (h3 : (3 : K) = 0) (A : SL(2, K)) {v : V} (h₀ : polar Q v w₀ = 0)
    (h₁ : polar Q v w₁ = 0) (h₂ : polar Q v w₂ = 0) (h₃ : polar Q v w₃ = 0) :
    (h.frame h3).La A v = v := by
  refine Frame.La_apply_of_coords_eq_zero _ A ?_
  have hc : ∀ c₀ c₁ c₂ c₃ : K, polar Q v (comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃) = 0 := by
    intro c₀ c₁ c₂ c₃
    simp only [comb4, polar_add_right, polar_smul_right, h₀, h₁, h₂, h₃, smul_zero, add_zero]
  rw [Frame.coords_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Frame.f₁, Frame.f₂, Frame.e₁, Frame.e₂, frame, hc]

theorem La_neg_one_comb (h3 : (3 : K) = 0) (c₀ c₁ c₂ c₃ : K) :
    (h.frame h3).La (-1) (comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃) = -comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃ := by
  have h1 : comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃ = (h.frame h3).incl (c₀ • 1 +
      c₁ • ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) +
      c₂ • ((sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) +
      c₃ • (((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        ((sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))) := by
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h.incl_one h3,
      h.incl_sl2I h3, h.incl_sl2J h3, h.incl_sl2IJ h3]
    rfl
  rw [h1, Frame.La_apply_incl, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.neg_mul, Matrix.one_mul, map_neg]

theorem span_le (h3 : (3 : K) = 0) {W : Submodule K V} (h₀ : w₀ ∈ W) (h₁ : w₁ ∈ W)
    (h₂ : w₂ ∈ W) (h₃ : w₃ ∈ W) : (h.frame h3).span ≤ W := by
  rintro _ ⟨M, rfl⟩
  rw [h.incl_frame h3]
  exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ h₀) (W.smul_mem _ h₁))
    (W.smul_mem _ h₂)) (W.smul_mem _ h₃)

end OrthoQuad

structure QuatQuad (Q : QuadraticForm K V) (W : Submodule K V) (X Y : V ≃ₗ[K] V) (v₀ : V) :
    Prop where
  memX : X ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  memY : Y ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  mapX : ∀ v ∈ W, X v ∈ W
  mapY : ∀ v ∈ W, Y v ∈ W
  XX : ∀ v ∈ W, X (X v) = -v
  YY : ∀ v ∈ W, Y (Y v) = -v
  YX : ∀ v ∈ W, Y (X v) = -X (Y v)
  mem : v₀ ∈ W
  Q_v₀ : Q v₀ = 1

namespace QuatQuad

variable {W : Submodule K V} {X Y : V ≃ₗ[K] V} {v₀ : V} (h : QuatQuad Q W X Y v₀)
include h

theorem XY_XY : (X * Y) ((X * Y) v₀) = -v₀ := by
  have h1 := h.YX _ (h.mapY _ h.mem)
  rw [h.YY _ h.mem, map_neg, neg_neg] at h1
  simp only [LinearEquiv.mul_apply]
  rw [h1, h.XX _ h.mem]

theorem orthoQuad (h3 : (3 : K) = 0) : OrthoQuad Q v₀ (X v₀) (Y v₀) (X (Y v₀)) := by
  have h2 := two_ne_zero_of h3
  have p01 := polar_eq_zero_of_mul_self h2 h.memX (h.XX _ h.mem)
  have p02 := polar_eq_zero_of_mul_self h2 h.memY (h.YY _ h.mem)
  have p03 : polar Q v₀ (X (Y v₀)) = 0 := by
    have := polar_eq_zero_of_mul_self h2 (mul_mem h.memX h.memY) h.XY_XY
    simpa only [LinearEquiv.mul_apply] using this
  refine ⟨h.Q_v₀, ?_, ?_, ?_, p01, p02, p03, ?_, ?_, ?_⟩
  · rw [map_of_mem h.memX, h.Q_v₀]
  · rw [map_of_mem h.memY, h.Q_v₀]
  · rw [map_of_mem h.memX, map_of_mem h.memY, h.Q_v₀]
  · rw [← polar_map_of_mem h.memX, h.XX _ h.mem, polar_neg_left, p03, neg_zero]
  · rw [polar_map_of_mem h.memX, p02]
  · have h1 := h.YX _ h.mem
    rw [show X (Y v₀) = -Y (X v₀) by rw [h1, neg_neg], polar_neg_right,
      polar_map_of_mem h.memY, p01, neg_zero]

theorem X_comb (c₀ c₁ c₂ c₃ : K) :
    X (comb4 v₀ (X v₀) (Y v₀) (X (Y v₀)) c₀ c₁ c₂ c₃) =
      comb4 v₀ (X v₀) (Y v₀) (X (Y v₀)) (-c₁) c₀ (-c₃) c₂ := by
  simp only [comb4, map_add, map_smul, h.XX _ h.mem, h.XX _ (h.mapY _ h.mem)]
  module

theorem Y_comb (c₀ c₁ c₂ c₃ : K) :
    Y (comb4 v₀ (X v₀) (Y v₀) (X (Y v₀)) c₀ c₁ c₂ c₃) =
      comb4 v₀ (X v₀) (Y v₀) (X (Y v₀)) (-c₂) c₃ c₀ (-c₁) := by
  have h1 := h.YX _ h.mem
  have h2 := h.YX _ (h.mapY _ h.mem)
  rw [h.YY _ h.mem, map_neg, neg_neg] at h2
  simp only [comb4, map_add, map_smul, h1, h2, h.YY _ h.mem]
  module

end QuatQuad

theorem exists_frame_of_quat (h3 : (3 : K) = 0) {W : Submodule K V} {X Y : V ≃ₗ[K] V} {v₀ : V}
    (h : QuatQuad Q W X Y v₀) :
    ∃ F : Frame Q, F.span ≤ W ∧
      (∀ M, X (F.incl M) = F.incl (((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * M)) ∧
      ∀ M, Y (F.incl M) = F.incl (((sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * M) := by
  have ho := h.orthoQuad h3
  refine ⟨ho.frame h3, ho.span_le h3 h.mem (h.mapX _ h.mem) (h.mapY _ h.mem)
    (h.mapX _ (h.mapY _ h.mem)), fun M => ?_, fun M => ?_⟩
  · rw [ho.incl_frame h3, ho.incl_frame h3, h.X_comb]
    simp only [coe_sl2I, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact comb4_congr (by ring) (by ring) (by ring) (by ring)
  · rw [ho.incl_frame h3, ho.incl_frame h3, h.Y_comb]
    simp only [coe_sl2J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact comb4_congr (by ring) (by ring) (by linear_combination (-(M 0 0) - M 1 1) * h3)
      (by linear_combination (M 0 1 - M 1 0) * h3)

end CFSG.ClassicalInvolution.Q3.TL4.OrthQ8
