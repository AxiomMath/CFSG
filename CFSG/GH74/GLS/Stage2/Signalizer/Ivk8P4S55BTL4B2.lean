module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4M

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Subgroup BS4
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def unipG : Subgroup (GL (Fin 2 ⊕ Fin 2) F) where
  carrier := {x | (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 ∧
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = 1 ∧
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ = 1}
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> ext i j <;>
      simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.one_apply]
  mul_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul]
      exact ll_mul hx1 hy1
    · rw [Units.val_mul, ul_mul hy1, hx2, hy2, Matrix.one_mul]
    · rw [Units.val_mul, lr_mul hx1, hx3, hy3, Matrix.one_mul]
  inv_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    set M := (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hM
    set N := ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hN
    have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    obtain ⟨Q, hQ⟩ : ∃ Q, M.toBlocks₁₂ = Q := ⟨_, rfl⟩
    have hA : M = fromBlocks 1 Q 0 1 := by
      conv_lhs => rw [← fromBlocks_toBlocks M]
      rw [hx1, hx2, hx3, hQ]
    have hMX : M * fromBlocks 1 (-Q) 0 1 = 1 := by
      rw [hA, fromBlocks_multiply, ← fromBlocks_one]
      simp
    have hNeq : N = fromBlocks 1 (-Q) 0 1 := by
      calc N = N * (M * fromBlocks 1 (-Q) 0 1) := by rw [hMX, Matrix.mul_one]
        _ = fromBlocks 1 (-Q) 0 1 := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hN, hNeq, toBlocks_fromBlocks₂₁]
    · rw [← hN, hNeq, toBlocks_fromBlocks₁₁]
    · rw [← hN, hNeq, toBlocks_fromBlocks₂₂]

theorem eq_of_mem_unipG {x : GL (Fin 2 ⊕ Fin 2) F} (hx : x ∈ unipG) :
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks 1 (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₂ 0 1 := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  conv_lhs => rw [← fromBlocks_toBlocks (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)]
  rw [hx1, hx2, hx3]

theorem unipG_comm {x y : GL (Fin 2 ⊕ Fin 2) F} (hx : x ∈ unipG) (hy : y ∈ unipG) :
    x * y = y * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, eq_of_mem_unipG hx, eq_of_mem_unipG hy, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add]
  rw [add_comm]

theorem mul_mul_mul_eq_one {a b c d : Matrix (Fin 2) (Fin 2) F} (hac : a * c = 1)
    (hbd : b * d = 1) : b * a * c * d = 1 := by
  rw [Matrix.mul_assoc b, hac, Matrix.mul_one, hbd]

theorem ul_lr_inv {x : GL (Fin 2 ⊕ Fin 2) F}
    (hxi : ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ =
      0) (hx : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0) :
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ *
      ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = 1 ∧
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ *
      ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ = 1 := by
  have h1 : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [← ul_mul hxi, h1]
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  · rw [← lr_mul hx, h1]
    ext i j
    simp [Matrix.toBlocks₂₂, Matrix.one_apply]

theorem comm_of_blocks_comm {H : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    (hH : ∀ x ∈ H, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
    (hul : ∀ x ∈ H, ∀ y ∈ H, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ *
      (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ =
        (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ *
          (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁)
    (hlr : ∀ x ∈ H, ∀ y ∈ H, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ *
      (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ =
        (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂ *
          (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₂) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  have hle : ⁅H, H⁆ ≤ unipG := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxi := hH _ (inv_mem hx)
    have hyi := hH _ (inv_mem hy)
    obtain ⟨hx1, hx2⟩ := ul_lr_inv hxi (hH x hx)
    obtain ⟨hy1, hy2⟩ := ul_lr_inv hyi (hH y hy)
    rw [commutatorElement_def]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Units.val_mul]
      exact ll_mul (ll_mul (ll_mul (hH x hx) (hH y hy)) hxi) hyi
    · simp only [Units.val_mul]
      rw [ul_mul hyi, ul_mul hxi, ul_mul (hH y hy), hul x hx y hy]
      exact mul_mul_mul_eq_one hx1 hy1
    · simp only [Units.val_mul]
      rw [lr_mul (ll_mul (ll_mul (hH x hx) (hH y hy)) hxi), lr_mul (ll_mul (hH x hx) (hH y hy)),
        lr_mul (hH x hx), hlr x hx y hy]
      exact mul_mul_mul_eq_one hx2 hy2
  intro z hz w hw
  exact unipG_comm (hle hz) (hle hw)

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
