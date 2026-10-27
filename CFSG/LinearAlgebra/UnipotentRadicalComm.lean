module

public import CFSG.LinearAlgebra.UnipotentRadical

public section

open Matrix

namespace CFSG.LinearAlgebra

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem commute_of_mem_unipotentRadical {W : Submodule K (ι → K)} {g h : GL ι K}
    (hg : g ∈ unipotentRadical W) (hh : h ∈ unipotentRadical W) : g * h = h * g := by
  obtain ⟨hg1, hg2⟩ := mem_unipotentRadical_iff.mp hg
  obtain ⟨hh1, hh2⟩ := mem_unipotentRadical_iff.mp hh
  have key : ∀ x : ι → K, (g : Matrix ι ι K) *ᵥ ((h : Matrix ι ι K) *ᵥ x) =
      (h : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ x) := by
    intro x
    have h1 : (g : Matrix ι ι K) *ᵥ ((h : Matrix ι ι K) *ᵥ x) =
        x + ((g : Matrix ι ι K) *ᵥ x - x) + ((h : Matrix ι ι K) *ᵥ x - x) := by
      conv_lhs => rw [show (h : Matrix ι ι K) *ᵥ x =
        x + ((h : Matrix ι ι K) *ᵥ x - x) by rw [add_comm, sub_add_cancel]]
      rw [Matrix.mulVec_add, hg2 _ (hh1 x)]
      abel
    have h2 : (h : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ x) =
        x + ((h : Matrix ι ι K) *ᵥ x - x) + ((g : Matrix ι ι K) *ᵥ x - x) := by
      conv_lhs => rw [show (g : Matrix ι ι K) *ᵥ x =
        x + ((g : Matrix ι ι K) *ᵥ x - x) by rw [add_comm, sub_add_cancel]]
      rw [Matrix.mulVec_add, hh2 _ (hg1 x)]
      abel
    rw [h1, h2]
    abel
  refine Units.ext (Matrix.ext_iff_mulVec.2 fun x => ?_)
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact key x

end CFSG.LinearAlgebra
