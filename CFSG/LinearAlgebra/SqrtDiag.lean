module

public import Mathlib.FieldTheory.Perfect

public section

namespace CFSG.LinearAlgebra

open Matrix

variable {K : Type*} [Field K] [CharP K 2] [PerfectRing K 2] {n : Type*} [Fintype n]

noncomputable def sqrtDiag (S : Matrix n n K) : n → K :=
  fun i => (frobeniusEquiv K 2).symm (S i i)

theorem sqrtDiag_apply_sq (S : Matrix n n K) (i : n) : sqrtDiag S i ^ 2 = S i i := by
  simp [sqrtDiag]

theorem sqrtDiag_add (S T : Matrix n n K) : sqrtDiag (S + T) = sqrtDiag S + sqrtDiag T := by
  funext i
  simp [sqrtDiag]

theorem sqrtDiag_eq_zero_iff (S : Matrix n n K) : sqrtDiag S = 0 ↔ ∀ i, S i i = 0 := by
  constructor
  · intro h i
    have := congrFun h i
    simpa [sqrtDiag] using congrArg (frobeniusEquiv K 2) this
  · intro h
    funext i
    simp [sqrtDiag, h i]

theorem dotProduct_mulVec_self_eq_sq {S : Matrix n n K} (hS : Sᵀ = S) (x : n → K) :
    x ⬝ᵥ (S *ᵥ x) = (sqrtDiag S ⬝ᵥ x) ^ 2 := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  let Q : (n → K) →+ K :=
    { toFun := fun x => (S *ᵥ x) ⬝ᵥ x
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [mulVec_add, add_dotProduct, dotProduct_add]
        rw [show (S *ᵥ y) ⬝ᵥ x = (S *ᵥ x) ⬝ᵥ y from by
          rw [dotProduct_comm (S *ᵥ y) x, dotProduct_comm (S *ᵥ x) y]
          exact Matrix.IsSymm.dotProduct_mulVec_comm hS]
        linear_combination ((S *ᵥ x) ⬝ᵥ y) * h2 }
  let Q' : (n → K) →+ K :=
    { toFun := fun x => (sqrtDiag S ⬝ᵥ x) * (sqrtDiag S ⬝ᵥ x)
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [dotProduct_add]
        linear_combination ((sqrtDiag S ⬝ᵥ x) * (sqrtDiag S ⬝ᵥ y)) * h2 }
  have hQ : Q = Q' :=
    AddMonoidHom.functions_ext _ Q Q' fun i c => by
      change (S *ᵥ Pi.single i c) ⬝ᵥ Pi.single i c =
        (sqrtDiag S ⬝ᵥ Pi.single i c) * (sqrtDiag S ⬝ᵥ Pi.single i c)
      rw [dotProduct_single, dotProduct_single, mulVec_single]
      simp only [Pi.smul_apply, col_apply, op_smul_eq_smul, smul_eq_mul]
      rw [← sqrtDiag_apply_sq S i]
      ring
  have := DFunLike.congr_fun hQ x
  rw [dotProduct_comm x, pow_two]
  exact this

theorem sqrtDiag_mul_mul_transpose {S : Matrix n n K} (hS : Sᵀ = S) (g : Matrix n n K) :
    sqrtDiag (g * S * gᵀ) = g *ᵥ sqrtDiag S := by
  classical
  funext i
  have hdiag : (g * S * gᵀ) i i = (sqrtDiag S ⬝ᵥ g.row i) ^ 2 := by
    rw [show (g * S * gᵀ) i i = (g.row i ᵥ* S) ⬝ᵥ (g.row i) from rfl,
      ← Matrix.dotProduct_mulVec]
    exact dotProduct_mulVec_self_eq_sq hS (g.row i)
  rw [sqrtDiag, hdiag, frobeniusEquiv_symm_pow, Matrix.mulVec_apply]
  exact dotProduct_comm _ _

end CFSG.LinearAlgebra
