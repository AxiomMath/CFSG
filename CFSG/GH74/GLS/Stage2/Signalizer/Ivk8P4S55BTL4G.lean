module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4F3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Subgroup BS4
open scoped commutatorElement

variable {F : Type} [Field F]

theorem fromBlocks_diag_mul (a b c d : Matrix (Fin 2) (Fin 2) F) :
    fromBlocks a 0 0 b * fromBlocks c 0 0 d = fromBlocks (a * c) 0 0 (b * d) := by
  rw [fromBlocks_multiply]
  simp

@[expose] def detOne (h2 : (2 : F) ≠ 0) : Subgroup (GL (Fin 2 ⊕ Fin 2) F) where
  carrier := {y | dD * (y : MB F) = (y : MB F) * dD ∧ (y : MB F).toBlocks₁₁.det = 1 ∧
    (y : MB F).toBlocks₂₂.det = 1}
  one_mem' := by
    refine ⟨by simp, ?_, ?_⟩
    · show (1 : MB F).toBlocks₁₁.det = 1
      rw [← fromBlocks_one, toBlocks_fromBlocks₁₁, det_one]
    · show (1 : MB F).toBlocks₂₂.det = 1
      rw [← fromBlocks_one, toBlocks_fromBlocks₂₂, det_one]
  mul_mem' := by
    rintro x y ⟨hx, hx1, hx2⟩ ⟨hy, hy1, hy2⟩
    have ex := eq_fromBlocks_of_comm_dD h2 hx
    have ey := eq_fromBlocks_of_comm_dD h2 hy
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]
    · rw [Units.val_mul, ex, ey, fromBlocks_diag_mul, toBlocks_fromBlocks₁₁, det_mul, hx1, hy1,
        one_mul]
    · rw [Units.val_mul, ex, ey, fromBlocks_diag_mul, toBlocks_fromBlocks₂₂, det_mul, hx2, hy2,
        one_mul]
  inv_mem' := by
    rintro x ⟨hx, hx1, hx2⟩
    have hxi : dD * ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) =
        ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) * dD := by
      have h1 : ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) * (x : MB F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2' : (x : MB F) * ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc dD * ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F)
          = (((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) * (x : MB F)) * dD *
              ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) := by rw [h1, Matrix.one_mul]
        _ = ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) * (dD * (x : MB F)) *
              ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) := by
            rw [hx]
            simp only [Matrix.mul_assoc]
        _ = ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) * dD *
              ((x : MB F) * ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F)) := by
            simp only [Matrix.mul_assoc]
        _ = ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) * dD := by rw [h2', Matrix.mul_one]
    have hprod : (x : MB F) * ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [eq_fromBlocks_of_comm_dD h2 hx, eq_fromBlocks_of_comm_dD h2 hxi, fromBlocks_diag_mul,
      ← fromBlocks_one, fromBlocks_inj] at hprod
    obtain ⟨p1, -, -, p2⟩ := hprod
    refine ⟨hxi, ?_, ?_⟩
    · have := congrArg det p1
      rw [det_mul, hx1, one_mul, det_one] at this
      exact this
    · have := congrArg det p2
      rw [det_mul, hx2, one_mul, det_one] at this
      exact this

theorem comm_dD_mul {a b : MB F} (ha : dD * a = a * dD) (hb : dD * b = b * dD) :
    dD * (a * b) = (a * b) * dD := by
  rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]

theorem comm_of_orth_blocks (h2 : (2 : F) ≠ 0) {β : MB F} (hβs : βᵀ = β) (hβd : β.det ≠ 0)
    (hβD : dD * β = β * dD) {H : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    (hHD : ∀ x ∈ H, dD * (x : MB F) = (x : MB F) * dD)
    (hHβ : ∀ x ∈ H, (x : MB F)ᵀ * β * (x : MB F) = β) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  have eβ := eq_fromBlocks_of_comm_dD h2 hβD
  have hst := hβs
  rw [eβ, fromBlocks_transpose, transpose_zero, fromBlocks_inj] at hst
  obtain ⟨hs1, -, -, hs2⟩ := hst
  have hd : β.toBlocks₁₁.det * β.toBlocks₂₂.det ≠ 0 := by
    rw [← det_fromBlocks_zero₂₁ β.toBlocks₁₁ 0 β.toBlocks₂₂, ← eβ]
    exact hβd
  have hblk : ∀ x ∈ H, (x : MB F).toBlocks₁₁ᵀ * β.toBlocks₁₁ * (x : MB F).toBlocks₁₁ =
      β.toBlocks₁₁ ∧ (x : MB F).toBlocks₂₂ᵀ * β.toBlocks₂₂ * (x : MB F).toBlocks₂₂ =
        β.toBlocks₂₂ := by
    intro x hx
    have h := hHβ x hx
    rw [eq_fromBlocks_of_comm_dD h2 (hHD x hx), eβ, fromBlocks_transpose, transpose_zero,
      fromBlocks_diag_mul, fromBlocks_diag_mul, fromBlocks_inj] at h
    exact ⟨h.1, h.2.2.2⟩
  have hdi : ∀ z ∈ H, (z : MB F).toBlocks₁₁.det *
      ((z⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁.det = 1 ∧
      (z : MB F).toBlocks₂₂.det * ((z⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂.det = 1 := by
    intro z hz
    have hp : (z : MB F) * ((z⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [eq_fromBlocks_of_comm_dD h2 (hHD z hz), eq_fromBlocks_of_comm_dD h2 (hHD _ (inv_mem hz)),
      fromBlocks_diag_mul, ← fromBlocks_one, fromBlocks_inj] at hp
    exact ⟨by rw [← det_mul, hp.1, det_one], by rw [← det_mul, hp.2.2.2, det_one]⟩
  have hle : ⁅H, H⁆ ≤ detOne h2 := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hD := fun z (hz : z ∈ H) => hHD z hz
    rw [commutatorElement_def]
    obtain ⟨hx1, hx2⟩ := hdi x hx
    obtain ⟨hy1, hy2⟩ := hdi y hy
    refine ⟨?_, ?_, ?_⟩
    · simp only [Units.val_mul]
      exact comm_dD_mul (comm_dD_mul (comm_dD_mul (hD x hx) (hD y hy)) (hD _ (inv_mem hx)))
        (hD _ (inv_mem hy))
    · simp only [Units.val_mul]
      rw [eq_fromBlocks_of_comm_dD h2 (hD x hx), eq_fromBlocks_of_comm_dD h2 (hD y hy),
        eq_fromBlocks_of_comm_dD h2 (hD _ (inv_mem hx)),
        eq_fromBlocks_of_comm_dD h2 (hD _ (inv_mem hy)), fromBlocks_diag_mul, fromBlocks_diag_mul,
        fromBlocks_diag_mul, toBlocks_fromBlocks₁₁, det_mul, det_mul, det_mul]
      linear_combination (((y : MB F).toBlocks₁₁.det *
        ((y⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁.det)) * hx1 + hy1
    · simp only [Units.val_mul]
      rw [eq_fromBlocks_of_comm_dD h2 (hD x hx), eq_fromBlocks_of_comm_dD h2 (hD y hy),
        eq_fromBlocks_of_comm_dD h2 (hD _ (inv_mem hx)),
        eq_fromBlocks_of_comm_dD h2 (hD _ (inv_mem hy)), fromBlocks_diag_mul, fromBlocks_diag_mul,
        fromBlocks_diag_mul, toBlocks_fromBlocks₂₂, det_mul, det_mul, det_mul]
      linear_combination (((y : MB F).toBlocks₂₂.det *
        ((y⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂.det)) * hx2 + hy2
  intro z hz w hw
  have hzH := Subgroup.commutator_le_self H hz
  have hwH := Subgroup.commutator_le_self H hw
  obtain ⟨-, hz1, hz2⟩ := hle hz
  obtain ⟨-, hw1, hw2⟩ := hle hw
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, eq_fromBlocks_of_comm_dD h2 (hHD z hzH),
    eq_fromBlocks_of_comm_dD h2 (hHD w hwH), fromBlocks_diag_mul, fromBlocks_diag_mul,
    comm_of_so2 h2 hs1 (left_ne_zero_of_mul hd) hz1 (hblk z hzH).1 hw1 (hblk w hwH).1,
    comm_of_so2 h2 hs2 (right_ne_zero_of_mul hd) hz2 (hblk z hzH).2 hw2 (hblk w hwH).2]

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
