module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4G3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4G

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open scoped commutatorElement

variable {F : Type} [Field F]

theorem inv_mul_self (P : GL (Fin 4) F) :
    ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem mul_inv_self (P : GL (Fin 4) F) :
    (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conj_mul_conj (P : GL (Fin 4) F) (X Y : Matrix (Fin 4) (Fin 4) F) :
    ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X * (P : Matrix (Fin 4) (Fin 4) F) *
      (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Y * (P : Matrix (Fin 4) (Fin 4) F)) =
    ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (X * Y) *
      (P : Matrix (Fin 4) (Fin 4) F) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) F), mul_inv_self, Matrix.one_mul]

theorem det_transpose_mul_ne_zero (P : GL (Fin 4) F) {β : Matrix (Fin 4) (Fin 4) F}
    (hβd : β.det ≠ 0) :
    ((P : Matrix (Fin 4) (Fin 4) F)ᵀ * β * (P : Matrix (Fin 4) (Fin 4) F)).det ≠ 0 := by
  have hP := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
  rw [det_mul, det_mul, det_transpose]
  exact mul_ne_zero (mul_ne_zero hP.ne_zero hβd) hP.ne_zero

theorem caseG1 (hK : ringChar F ≠ 2) {H : Subgroup (GL (Fin 4) F)} {B : GL (Fin 4) F}
    (hB2 : B * B = 1) (hfr : finrank F (LinearMap.ker (toLin' B.val - 1)) = 2)
    (hBH : ∀ x ∈ H, B * x = x * B) {β : Matrix (Fin 4) (Fin 4) F} (hβs : βᵀ = β)
    (hβd : β.det ≠ 0) (hHβ : ∀ x ∈ H, (x : Matrix (Fin 4) (Fin 4) F)ᵀ * β * x = β)
    (hBβ : (B : Matrix (Fin 4) (Fin 4) F)ᵀ * β = β * B) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨P, hP⟩ := exists_conj_diag4 hK hB2 hfr
  have hPm : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) *
      (P : Matrix (Fin 4) (Fin 4) F) = diag4 := by rw [← hP, Units.val_mul, Units.val_mul]
  refine comm_of_map (cbv_injective P) (comm_of_orth_blocks h2
    (β := bv ((P : Matrix (Fin 4) (Fin 4) F)ᵀ * β * (P : Matrix (Fin 4) (Fin 4) F)))
    ?_ ?_ ?_ ?_ ?_)
  · rw [← bv_transpose, transpose_mul, transpose_mul, transpose_transpose, hβs,
      Matrix.mul_assoc]
  · rw [det_bv]
    exact det_transpose_mul_ne_zero P hβd
  · have e := selfAdj_conj (mul_inv_self P) hBβ
    rw [hPm, diagonal_transpose] at e
    have e' := congrArg bv e
    rwa [map_mul bv (diag4 : Matrix (Fin 4) (Fin 4) F),
      map_mul bv ((P : Matrix (Fin 4) (Fin 4) F)ᵀ * β * (P : Matrix (Fin 4) (Fin 4) F)),
      bv_diag4] at e'
  · rintro _ ⟨x, hx, rfl⟩
    have hBx : (B : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) =
        (x : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) := by
      rw [← Units.val_mul, ← Units.val_mul, hBH x hx]
    rw [coe_cbv, ← bv_diag4, ← hPm, ← map_mul, ← map_mul, conj_mul_conj, conj_mul_conj, hBx]
  · rintro _ ⟨x, hx, rfl⟩
    rw [coe_cbv, ← bv_transpose, ← map_mul, ← map_mul]
    exact congrArg bv (transpose_conj_mul (mul_inv_self P) (hHβ x hx))

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
