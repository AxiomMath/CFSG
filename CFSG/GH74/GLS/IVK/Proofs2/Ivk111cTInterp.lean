module

public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Finset

section Interp

variable {F L : Type} [Field F] [Fintype F] [Field L] [Algebra F L]

theorem exists_interp {k : ℕ} (hk : k < Fintype.card F) :
    ∃ lam : F → L, ∀ k' < Fintype.card F,
      ∑ b : F, lam b * (algebraMap F L b) ^ k' = if k' = k then 1 else 0 := by
  classical
  let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
  let V : Matrix (Fin (Fintype.card F)) (Fin (Fintype.card F)) L :=
    Matrix.vandermonde (fun i => algebraMap F L (e.symm i))
  have hdet : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact e.symm.injective ((algebraMap F L).injective hij)
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨fun b => V⁻¹ ⟨k, hk⟩ (e b), fun k' hk' => ?_⟩
  have h1 := congrFun (congrFun hinv ⟨k, hk⟩) ⟨k', hk'⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  have h2 : ∑ b : F, V⁻¹ ⟨k, hk⟩ (e b) * (algebraMap F L b) ^ k' =
      ∑ i : Fin (Fintype.card F), V⁻¹ ⟨k, hk⟩ i * V i ⟨k', hk'⟩ := by
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [V, Matrix.vandermonde_apply]
  rw [h2, h1]
  simp [Fin.ext_iff, eq_comm]

end Interp

end CFSG.GH74.GLS.Stage4.Rest
