module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4F3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Subgroup BS4
open scoped commutatorElement

variable {F : Type} [Field F]

theorem det_toBlocks₁₂_ne_zero {β : MB F} (hβd : β.det ≠ 0) (hβ11 : β.toBlocks₁₁ = 0) :
    β.toBlocks₁₂.det ≠ 0 := by
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  apply hβd
  refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨Sum.elim w 0, fun h => hw0 ?_, ?_⟩
  · ext i
    simpa using congrFun h (Sum.inl i)
  · ext j
    rcases j with j | j
    · have e : ∀ i, β.toBlocks₁₁ i j = 0 := fun i => congrFun (congrFun hβ11 i) j
      simp only [vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      exact Finset.sum_eq_zero fun i _ => by
        have := e i
        simp only [toBlocks₁₁, of_apply] at this
        rw [this, mul_zero]
    · have := congrFun hw j
      simp only [vecMul, dotProduct, toBlocks₁₂, of_apply, Pi.zero_apply] at this
      simp only [vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      exact this

theorem toBlocks₁₂_transpose_mul {β x : MB F} (hβ11 : β.toBlocks₁₁ = 0)
    (hx : x.toBlocks₂₁ = 0) :
    (xᵀ * β * x).toBlocks₁₂ = x.toBlocks₁₁ᵀ * β.toBlocks₁₂ * x.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks x, ← fromBlocks_toBlocks β]
  rw [hx, hβ11, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    toBlocks_fromBlocks₁₂]
  simp [Matrix.mul_assoc]

theorem comm_of_rel {a a' d d' M : Matrix (Fin 2) (Fin 2) F} (hM : M.det ≠ 0)
    (ha : a.det ≠ 0) (ha' : a'.det ≠ 0) (hc : a * a' = a' * a) (h1 : aᵀ * M * d = M)
    (h2 : a'ᵀ * M * d' = M) : d * d' = d' * d := by
  have e1 : (a * a')ᵀ * M * (d * d') = M := by
    calc (a * a')ᵀ * M * (d * d') = a'ᵀ * (aᵀ * M * d) * d' := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = M := by rw [h1, h2]
  have e2 : (a' * a)ᵀ * M * (d' * d) = M := by
    calc (a' * a)ᵀ * M * (d' * d) = aᵀ * (a'ᵀ * M * d') * d := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = M := by rw [h2, h1]
  rw [hc] at e1
  have hT : IsUnit ((a' * a)ᵀ * M) := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [det_mul, det_transpose, det_mul]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha' ha) hM))
  exact hT.mul_left_cancel (e1.trans e2.symm)

theorem comm_of_lagr_blocks {β : MB F} (hβd : β.det ≠ 0) (hβ11 : β.toBlocks₁₁ = 0)
    {Bm : MB F} (hB21 : Bm.toBlocks₂₁ = 0) (hBns : ∀ c : F, Bm.toBlocks₁₁ ≠ c • 1)
    {H : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    (hH21 : ∀ x ∈ H, (x : MB F).toBlocks₂₁ = 0)
    (hHB : ∀ x ∈ H, Bm * (x : MB F) = (x : MB F) * Bm)
    (hHβ : ∀ x ∈ H, (x : MB F)ᵀ * β * (x : MB F) = β) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  have hul : ∀ x ∈ H, Bm.toBlocks₁₁ * (x : MB F).toBlocks₁₁ =
      (x : MB F).toBlocks₁₁ * Bm.toBlocks₁₁ := by
    intro x hx
    have := congrArg toBlocks₁₁ (hHB x hx)
    rwa [ul_mul (hH21 x hx), ul_mul hB21] at this
  have hrel : ∀ x ∈ H, (x : MB F).toBlocks₁₁ᵀ * β.toBlocks₁₂ * (x : MB F).toBlocks₂₂ =
      β.toBlocks₁₂ := by
    intro x hx
    rw [← toBlocks₁₂_transpose_mul hβ11 (hH21 x hx), hHβ x hx]
  have hdet11 : ∀ x ∈ H, (x : MB F).toBlocks₁₁.det ≠ 0 := by
    intro x hx h0
    have hu := (x : GL (Fin 2 ⊕ Fin 2) F).isUnit
    rw [Matrix.isUnit_iff_isUnit_det, ← fromBlocks_toBlocks (x : MB F), hH21 x hx,
      det_fromBlocks_zero₂₁, h0, zero_mul] at hu
    exact not_isUnit_zero hu
  have hβ12 := det_toBlocks₁₂_ne_zero hβd hβ11
  exact comm_of_blocks_comm hH21 (fun x hx y hy =>
    comm_of_comm_nonscalar hBns (hul x hx).symm (hul y hy).symm) (fun x hx y hy =>
      comm_of_rel hβ12 (hdet11 x hx) (hdet11 y hy)
        (comm_of_comm_nonscalar hBns (hul x hx).symm (hul y hy).symm) (hrel x hx) (hrel y hy))

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
