module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullAffine
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeCentralizerComplement

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords

open Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "𝔽" => Fin 3 → ZMod 2

@[expose] def uv (k : Fin 3) : 𝔽 := Pi.single k 1

@[expose] def col (B : M₃) (k : Fin 3) : 𝔽 := fun i => B i k

@[expose] def sqS (v : 𝔽) : 𝕊 :=
  ⟨vecMulVec v v, MatrixExtension.vecMulVec_self_mem_binarySymMatrices v⟩

@[expose] def symPart (B : M₃) : 𝕊 :=
  ⟨B + Bᵀ, by rw [mem_binarySymMatrices, transpose_add, transpose_transpose, add_comm]⟩

theorem coe_sqS (v : 𝔽) : (sqS v : M₃) = vecMulVec v v :=
  rfl

theorem coe_symPart (B : M₃) : (symPart B : M₃) = B + Bᵀ :=
  rfl

theorem uv_zero : uv 0 = ![1, 0, 0] := by
  decide

theorem fix_stab_one : ∀ S : M₃,
    (glTransTwoOne : M₃) * S * (glTransTwoOne : M₃)ᵀ = S →
    (glTransThreeOne : M₃) * S * (glTransThreeOne : M₃)ᵀ = S →
    (glTransThreeTwo : M₃) * S * (glTransThreeTwo : M₃)ᵀ = S →
    (glSwapTwoThree : M₃) * S * (glSwapTwoThree : M₃)ᵀ = S →
    S = 0 ∨ S = vecMulVec ![1, 0, 0] ![1, 0, 0] := by
  decide +kernel

theorem glTransTwoOne_uv : (glTransTwoOne : M₃) *ᵥ uv 0 = uv 0 := by
  decide

theorem glTransThreeOne_uv : (glTransThreeOne : M₃) *ᵥ uv 0 = uv 0 := by
  decide

theorem glTransThreeTwo_uv : (glTransThreeTwo : M₃) *ᵥ uv 0 = uv 0 := by
  decide

theorem glSwapTwoThree_uv : (glSwapTwoThree : M₃) *ᵥ uv 0 = uv 0 := by
  decide

theorem exists_gl_e1 {v : 𝔽} (hv : v ≠ 0) : ∃ g : GL (Fin 3) (ZMod 2), (g : M₃) *ᵥ uv 0 = v := by
  obtain ⟨e, he, hve⟩ := exists_ne_zero_ne v
  obtain ⟨g, hg, -⟩ := exists_gl_pair hv he hve
  exact ⟨g, by rw [uv_zero, hg]⟩

theorem congr_vecMulVec (g : M₃) (w x : 𝔽) :
    g * vecMulVec w x * gᵀ = vecMulVec (g *ᵥ w) (g *ᵥ x) := by
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

theorem eq_sum_col (B : M₃) :
    B = vecMulVec (col B 0) (uv 0) + vecMulVec (col B 1) (uv 1) + vecMulVec (col B 2) (uv 2) := by
  ext i j
  fin_cases j <;> simp [vecMulVec_apply, col, uv]

theorem vecMulVec_add_add (w x : 𝔽) :
    vecMulVec (w + x) (w + x) = vecMulVec w w + vecMulVec x x + symThreePolar w x := by
  rw [add_vecMulVec, vecMulVec_add, vecMulVec_add, symThreePolar]
  abel

theorem two_eq_zero_mat (B : M₃) : B + B = 0 := by
  ext i j
  change B i j + B i j = 0
  generalize B i j = a
  revert a
  decide

theorem vec_add_self (v : 𝔽) : v + v = 0 := by
  funext i
  change v i + v i = 0
  generalize v i = a
  revert a
  decide

theorem symThreePolar_eq (w x : 𝔽) :
    symThreePolar w x = vecMulVec (w + x) (w + x) + vecMulVec w w + vecMulVec x x := by
  rw [vecMulVec_add_add]
  have h1 := two_eq_zero_mat (vecMulVec w w)
  have h2 := two_eq_zero_mat (vecMulVec x x)
  calc symThreePolar w x = symThreePolar w x + (vecMulVec w w + vecMulVec w w) +
        (vecMulVec x x + vecMulVec x x) := by rw [h1, h2, add_zero, add_zero]
    _ = _ := by abel


theorem sym_entry (S : 𝕊) (i j : Fin 3) : (S : M₃) j i = (S : M₃) i j :=
  congrFun (congrFun S.2 i) j

theorem sym_eq_sum (S : 𝕊) :
    S = symThreePolarSym ((S : M₃) 1 0 • uv 1) (uv 0) +
      symThreePolarSym ((S : M₃) 2 0 • uv 2) (uv 0) +
      symThreePolarSym ((S : M₃) 2 1 • uv 2) (uv 1) + sqS ((S : M₃) 0 0 • uv 0) +
      sqS ((S : M₃) 1 1 • uv 1) + sqS ((S : M₃) 2 2 • uv 2) := by
  apply Subtype.ext
  have hsq : ∀ a : ZMod 2, a * a = a := by decide
  have h01 := sym_entry S 0 1
  have h02 := sym_entry S 0 2
  have h12 := sym_entry S 1 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symThreePolarSym, symThreePolar, sqS, vecMulVec_apply, uv, hsq, h01, h02, h12]

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords
