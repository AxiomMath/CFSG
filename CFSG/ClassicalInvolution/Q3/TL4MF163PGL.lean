module

public import CFSG.ClassicalInvolution.Q3.TL4MF163Mat
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

namespace MF163

open Matrix

variable {K : Type*} [Field K]

section Order4

variable {A : Matrix (Fin 2) (Fin 2) K} (hA2 : ∀ a : K, A * A ≠ a • 1)
  (hA4 : ∃ a : K, A * A * (A * A) = a • 1)
include hA2 hA4

theorem scalar_or_smul_of_comm (h2 : (2 : K) ≠ 0) {B : Matrix (Fin 2) (Fin 2) K}
    (hB : B.det ≠ 0) {u : K} (hcomm : B * A = u • (A * B)) (hBB : ∃ a : K, B * B = a • 1) :
    (∃ a : K, B = a • 1) ∨ ∃ a : K, B = a • twoTraceless A := by
  have ht := trace_ne_zero hA2
  have hd := det_ne_zero_of_order4 hA2 hA4
  have hu : u = 1 := by
    have hdet := congrArg Matrix.det hcomm
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at hdet
    have hu2 : (u - 1) * (u + 1) * (A.det * B.det) = 0 := by linear_combination -hdet
    rcases mul_eq_zero.1 hu2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linear_combination h
      · exfalso
        have hu' : u = -1 := by linear_combination h
        have h3 : B * A * adjugate B = (-B.det) • A := by
          rw [hcomm, hu', neg_one_smul, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_adjugate,
            Matrix.mul_smul, Matrix.mul_one, neg_smul]
        have hcyc := Matrix.trace_mul_cycle B A (adjugate B)
        rw [h3, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
          Matrix.trace_smul, smul_eq_mul, smul_eq_mul] at hcyc
        have h4 : (2 * B.det) * A.trace = 0 := by linear_combination -hcyc
        rcases mul_eq_zero.1 h4 with h | h
        · exact mul_ne_zero h2 hB h
        · exact ht h
    · exact absurd h (mul_ne_zero hd hB)
  subst hu
  rw [one_smul] at hcomm
  obtain ⟨a, ha⟩ := hBB
  by_cases htB : B.trace = 0
  · right
    set N := twoTraceless A with hNdef
    have hBN : B * N = N * B := by
      rw [hNdef, twoTraceless, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        hcomm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have h4 : B * N + N * B = (B * N).trace • (1 : Matrix (Fin 2) (Fin 2) K) :=
      traceless_anticomm htB (trace_twoTraceless A)
    rw [← hBN] at h4
    have hNN : N * N = (-(2 * A.det)) • (1 : Matrix (Fin 2) (Fin 2) K) :=
      twoTraceless_mul_self hA2 hA4
    have h5 : (-(4 * A.det)) • B = (B * N).trace • N := by
      have h6 := congrArg (· * N) h4
      simp only [Matrix.add_mul, Matrix.mul_assoc, hNN, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one] at h6
      rw [← h6]
      module
    have hc : -(4 * A.det) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (by
      rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) hd)
    refine ⟨(-(4 * A.det))⁻¹ * (B * N).trace, ?_⟩
    rw [mul_smul, ← h5, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · left
    have h6 := mul_self_eq B
    rw [ha] at h6
    have h7 : B.trace • B = (a + B.det) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [add_smul, h6]
      abel
    refine ⟨(B.trace)⁻¹ * (a + B.det), ?_⟩
    rw [mul_smul, ← h7, smul_smul, inv_mul_cancel₀ htB, one_smul]

end Order4

section PGL

open Matrix.ProjGenLinGroup
open scoped MatrixGroups

theorem det_ne_zero_of_GL (g : GL (Fin 2) K) : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.ne_zero _

theorem scalar_val (u : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem mk_eq_one_iff {g : GL (Fin 2) K} :
    mk g = 1 ↔ ∃ a : K, (g : Matrix (Fin 2) (Fin 2) K) = a • 1 := by
  rw [mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, scalar_val u⟩
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply det_ne_zero_of_GL g
      rw [ha, zero_smul, Matrix.det_zero]
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Units.ext
    rw [scalar_val, ha, Units.val_mk0]

theorem mk_eq_mk_of_smul {g₁ g₂ : GL (Fin 2) K} {s : K} (hs : s ≠ 0)
    (h : (g₁ : Matrix (Fin 2) (Fin 2) K) = s • (g₂ : Matrix (Fin 2) (Fin 2) K)) :
    mk g₁ = mk g₂ := by
  rw [mk_eq_mk_iff]
  refine ⟨(Units.mk0 s hs)⁻¹, ?_⟩
  apply Units.ext
  rw [Units.val_mul, scalar_val, h, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hs, one_smul]

theorem not_scalar_of_sq {C : GL (Fin 2) K} (hc2 : mk C ^ 2 ≠ 1) :
    ∀ a : K, (C : Matrix (Fin 2) (Fin 2) K) * C ≠ a • 1 := by
  intro a ha
  apply hc2
  rw [← map_pow, mk_eq_one_iff]
  exact ⟨a, by rw [sq, Units.val_mul]; exact ha⟩

theorem scalar_of_pow_four {C : GL (Fin 2) K} (hc4 : mk C ^ 4 = 1) :
    ∃ a : K, (C : Matrix (Fin 2) (Fin 2) K) * C * (C * C) = a • 1 := by
  rw [← map_pow, mk_eq_one_iff] at hc4
  obtain ⟨a, ha⟩ := hc4
  refine ⟨a, ?_⟩
  rw [← ha, show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, Units.val_mul, Units.val_mul]

theorem pgl2_mul_self_of_inv (h2 : (2 : K) ≠ 0) {c w : PGL(2, K)} (hc2 : c ^ 2 ≠ 1)
    (hc4 : c ^ 4 = 1) (hw : w * c * w⁻¹ = c⁻¹) : w * w = 1 := by
  induction c using Matrix.ProjGenLinGroup.induction_on with | mk C => ?_
  induction w using Matrix.ProjGenLinGroup.induction_on with | mk W => ?_
  have hA2 := not_scalar_of_sq hc2
  have hA4 := scalar_of_pow_four hc4
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, mk_eq_mk_iff] at hw
  obtain ⟨u, hu⟩ := hw
  have h1 : W * C * W⁻¹ = C⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ := by
    rw [← hu]
    group
  have hGL : C * W * C = Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * W := by
    rw [map_inv]
    calc C * W * C = C * ((W * C * W⁻¹) * W) := by group
      _ = C * (C⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ * W) := by rw [h1]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ * W := by group
  have hrel : (C : Matrix (Fin 2) (Fin 2) K) * (W : Matrix (Fin 2) (Fin 2) K) *
      (C : Matrix (Fin 2) (Fin 2) K) = ((u⁻¹ : Kˣ) : K) • (W : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg Units.val hGL
    rw [Units.val_mul, Units.val_mul, Units.val_mul, scalar_val, Matrix.smul_mul,
      Matrix.one_mul] at this
    exact this
  obtain ⟨a, ha⟩ := mul_self_scalar_of_rel hA2 hA4 h2 (det_ne_zero_of_GL W) hrel
  rw [← map_mul, mk_eq_one_iff]
  exact ⟨a, by rw [Units.val_mul]; exact ha⟩

theorem pgl2_eq_of_comm (h2 : (2 : K) ≠ 0) {c b : PGL(2, K)} (hc2 : c ^ 2 ≠ 1) (hc4 : c ^ 4 = 1)
    (hb : b * c = c * b) (hbb : b * b = 1) : b = 1 ∨ b = c ^ 2 := by
  induction c using Matrix.ProjGenLinGroup.induction_on with | mk C => ?_
  induction b using Matrix.ProjGenLinGroup.induction_on with | mk B => ?_
  have hA2 := not_scalar_of_sq hc2
  have hA4 := scalar_of_pow_four hc4
  rw [← map_mul, ← map_mul, mk_eq_mk_iff] at hb
  obtain ⟨u, hu⟩ := hb
  have hGL : B * C = C * B * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by
    rw [map_inv, ← hu]
    group
  have hcomm : (B : Matrix (Fin 2) (Fin 2) K) * (C : Matrix (Fin 2) (Fin 2) K) =
      ((u⁻¹ : Kˣ) : K) • ((C : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K)) := by
    have := congrArg Units.val hGL
    rw [Units.val_mul, Units.val_mul, Units.val_mul, scalar_val, Matrix.mul_smul,
      Matrix.mul_one] at this
    exact this
  have hBB : ∃ a : K, (B : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) =
      a • 1 := by
    rw [← map_mul, mk_eq_one_iff] at hbb
    obtain ⟨a, ha⟩ := hbb
    exact ⟨a, by rw [← Units.val_mul]; exact ha⟩
  rcases scalar_or_smul_of_comm hA2 hA4 h2 (det_ne_zero_of_GL B) hcomm hBB with ⟨a, ha⟩ | ⟨a, ha⟩
  · left
    rw [mk_eq_one_iff]
    exact ⟨a, ha⟩
  · right
    have ht := trace_ne_zero hA2
    have h2C := two_mul_self_eq_smul hA2 hA4
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply det_ne_zero_of_GL B
      rw [ha, zero_smul, Matrix.det_zero]
    rw [← map_pow]
    refine mk_eq_mk_of_smul (s := 2 * a / (C : Matrix (Fin 2) (Fin 2) K).trace)
      (div_ne_zero (mul_ne_zero h2 ha0) ht) ?_
    rw [sq, Units.val_mul, ha, show (2 * a / (C : Matrix (Fin 2) (Fin 2) K).trace) •
        ((C : Matrix (Fin 2) (Fin 2) K) * C) = (a / (C : Matrix (Fin 2) (Fin 2) K).trace) •
          ((2 : K) • ((C : Matrix (Fin 2) (Fin 2) K) * C)) by
        rw [smul_smul]; congr 1; ring, h2C, smul_smul, div_mul_cancel₀ a ht]

end PGL

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
