module

public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

section Sigma

variable {E : Type} [Field E]

@[expose] def unitaryJ6 : Matrix (Fin 6) (Fin 6) E :=
  !![0, 0, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0; 0, 0, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0;
    0, -1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0]

@[expose] def unitaryJInv6 : Matrix (Fin 6) (Fin 6) E :=
  !![0, 0, 0, 0, 0, 1; 0, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 0; 0, 0, -1, 0, 0, 0;
    0, 1, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0]

theorem unitaryJ6_mul : (unitaryJ6 : Matrix (Fin 6) (Fin 6) E) * unitaryJInv6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryJ6, unitaryJInv6, Matrix.mul_apply, Fin.sum_univ_six]

private theorem unitaryJ6_apply (a i : Fin 6) :
    (unitaryJ6 : Matrix (Fin 6) (Fin 6) E) a i =
      if (a : ℕ) + (i : ℕ) = 5 then (-1 : E) ^ ((a : ℕ) + 1) else 0 := by
  fin_cases a <;> fin_cases i <;> norm_num [unitaryJ6]

private theorem unitaryJInv6_apply (j b : Fin 6) :
    (unitaryJInv6 : Matrix (Fin 6) (Fin 6) E) j b =
      if (j : ℕ) + (b : ℕ) = 5 then (-1 : E) ^ (j : ℕ) else 0 := by
  fin_cases j <;> fin_cases b <;> norm_num [unitaryJInv6]

private def revIdx (a : Fin 6) : Fin 6 := ⟨5 - (a : ℕ), by omega⟩

private theorem revIdx_val (a : Fin 6) : (revIdx a : ℕ) = 5 - (a : ℕ) := rfl

private theorem unitaryJ6_apply_self (a : Fin 6) :
    (unitaryJ6 : Matrix (Fin 6) (Fin 6) E) a (revIdx a) = (-1 : E) ^ ((a : ℕ) + 1) := by
  rw [unitaryJ6_apply, if_pos (by rw [revIdx_val]; omega)]

private theorem unitaryJ6_apply_eq_zero (a i : Fin 6) (h : i ≠ revIdx a) :
    (unitaryJ6 : Matrix (Fin 6) (Fin 6) E) a i = 0 := by
  rw [unitaryJ6_apply, if_neg]
  intro hc
  exact h (Fin.ext (by rw [revIdx_val]; omega))

private theorem unitaryJInv6_apply_self (b : Fin 6) :
    (unitaryJInv6 : Matrix (Fin 6) (Fin 6) E) (revIdx b) b =
      (-1 : E) ^ ((revIdx b : ℕ)) := by
  rw [unitaryJInv6_apply, if_pos (by rw [revIdx_val]; omega)]

private theorem unitaryJInv6_apply_eq_zero (j b : Fin 6) (h : j ≠ revIdx b) :
    (unitaryJInv6 : Matrix (Fin 6) (Fin 6) E) j b = 0 := by
  rw [unitaryJInv6_apply, if_neg]
  intro hc
  exact h (Fin.ext (by rw [revIdx_val]; omega))

private theorem unitaryJ6_mul_apply (X : Matrix (Fin 6) (Fin 6) E) (a b : Fin 6) :
    ((unitaryJ6 : Matrix (Fin 6) (Fin 6) E) * X) a b =
      (-1 : E) ^ ((a : ℕ) + 1) * X (revIdx a) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (revIdx a)]
  · rw [unitaryJ6_apply_self]
  · intro i _ hi
    rw [unitaryJ6_apply_eq_zero a i hi, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem unitaryJInv6_mul_apply (Y : Matrix (Fin 6) (Fin 6) E) (a b : Fin 6) :
    (Y * (unitaryJInv6 : Matrix (Fin 6) (Fin 6) E)) a b =
      Y a (revIdx b) * (-1 : E) ^ ((revIdx b : ℕ)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (revIdx b)]
  · rw [unitaryJInv6_apply_self]
  · intro j _ hj
    rw [unitaryJInv6_apply_eq_zero j b hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem unitaryJ6_conj_apply (X : Matrix (Fin 6) (Fin 6) E) (a b : Fin 6) :
    ((unitaryJ6 : Matrix (Fin 6) (Fin 6) E) * X * (unitaryJInv6 : Matrix (Fin 6) (Fin 6) E)) a b =
      (-1 : E) ^ ((a : ℕ) + 1) * X (revIdx a) (revIdx b) * (-1 : E) ^ ((revIdx b : ℕ)) := by
  rw [unitaryJInv6_mul_apply, unitaryJ6_mul_apply]

@[expose] def sigmaA6 (ψ : E ≃+* E) : SL(6, E) ≃* SL(6, E) :=
  (fieldAutSL ψ 6).trans ((invTransposeSL 6).trans (conjSL unitaryJ6 unitaryJInv6 unitaryJ6_mul))

private theorem coe_blockSL_six_zero (A : SL(2, E)) :
    ((blockSL E 6 2 0 (by omega) A : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      !![A 0 0, A 0 1, 0, 0, 0, 0; A 1 0, A 1 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
        0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

private theorem coe_blockSL_six_one (A : SL(2, E)) :
    ((blockSL E 6 2 1 (by omega) A : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      !![1, 0, 0, 0, 0, 0; 0, A 0 0, A 0 1, 0, 0, 0; 0, A 1 0, A 1 1, 0, 0, 0;
        0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

private theorem coe_blockSL_six_two (A : SL(2, E)) :
    ((blockSL E 6 2 2 (by omega) A : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, A 0 0, A 0 1, 0, 0;
        0, 0, A 1 0, A 1 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

private theorem coe_blockSL_six_three (A : SL(2, E)) :
    ((blockSL E 6 2 3 (by omega) A : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
        0, 0, 0, A 0 0, A 0 1, 0; 0, 0, 0, A 1 0, A 1 1, 0; 0, 0, 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

private theorem coe_blockSL_six_four (A : SL(2, E)) :
    ((blockSL E 6 2 4 (by omega) A : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
        0, 0, 0, 1, 0, 0; 0, 0, 0, 0, A 0 0, A 0 1; 0, 0, 0, 0, A 1 0, A 1 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

theorem sigmaA6_blockSL2 (ψ : E ≃+* E) (i : Fin 5) (A : SL(2, E)) :
    sigmaA6 ψ (blockSL2 E 5 i A) = blockSL2 E 5 (Fin.rev i) (fieldAutSL ψ 2 A) := by
  fin_cases i
  · show conjSL unitaryJ6 unitaryJInv6 unitaryJ6_mul
        (invTransposeSL 6 (fieldAutSL ψ 6 (blockSL E 6 2 0 (by omega) A))) =
          blockSL E 6 2 4 (by omega) (fieldAutSL ψ 2 A)
    rw [fieldAutSL_blockSL, invTransposeSL_blockSL]
    generalize fieldAutSL ψ 2 A = M
    refine Subtype.ext ?_
    simp only [coe_conjSL, coe_blockSL, coe_invTransposeSL_two]
    ext a b
    rw [unitaryJ6_conj_apply]
    fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, revIdx] <;> ring
  · show conjSL unitaryJ6 unitaryJInv6 unitaryJ6_mul
        (invTransposeSL 6 (fieldAutSL ψ 6 (blockSL E 6 2 1 (by omega) A))) =
          blockSL E 6 2 3 (by omega) (fieldAutSL ψ 2 A)
    rw [fieldAutSL_blockSL, invTransposeSL_blockSL]
    generalize fieldAutSL ψ 2 A = M
    refine Subtype.ext ?_
    simp only [coe_conjSL, coe_blockSL, coe_invTransposeSL_two]
    ext a b
    rw [unitaryJ6_conj_apply]
    fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, revIdx] <;> ring
  · show conjSL unitaryJ6 unitaryJInv6 unitaryJ6_mul
        (invTransposeSL 6 (fieldAutSL ψ 6 (blockSL E 6 2 2 (by omega) A))) =
          blockSL E 6 2 2 (by omega) (fieldAutSL ψ 2 A)
    rw [fieldAutSL_blockSL, invTransposeSL_blockSL]
    generalize fieldAutSL ψ 2 A = M
    refine Subtype.ext ?_
    simp only [coe_conjSL, coe_blockSL, coe_invTransposeSL_two]
    ext a b
    rw [unitaryJ6_conj_apply]
    fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, revIdx] <;> ring
  · show conjSL unitaryJ6 unitaryJInv6 unitaryJ6_mul
        (invTransposeSL 6 (fieldAutSL ψ 6 (blockSL E 6 2 3 (by omega) A))) =
          blockSL E 6 2 1 (by omega) (fieldAutSL ψ 2 A)
    rw [fieldAutSL_blockSL, invTransposeSL_blockSL]
    generalize fieldAutSL ψ 2 A = M
    refine Subtype.ext ?_
    simp only [coe_conjSL, coe_blockSL, coe_invTransposeSL_two]
    ext a b
    rw [unitaryJ6_conj_apply]
    fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, revIdx] <;> ring
  · show conjSL unitaryJ6 unitaryJInv6 unitaryJ6_mul
        (invTransposeSL 6 (fieldAutSL ψ 6 (blockSL E 6 2 4 (by omega) A))) =
          blockSL E 6 2 0 (by omega) (fieldAutSL ψ 2 A)
    rw [fieldAutSL_blockSL, invTransposeSL_blockSL]
    generalize fieldAutSL ψ 2 A = M
    refine Subtype.ext ?_
    simp only [coe_conjSL, coe_blockSL, coe_invTransposeSL_two]
    ext a b
    rw [unitaryJ6_conj_apply]
    fin_cases a <;> fin_cases b <;>
      simp [blockMat_apply, revIdx] <;> ring

end Sigma

section Group

variable {E : Type} [Field E] (θ : E →+* E) (hθ : ∀ c, θ (θ c) = c)

@[expose] def unitaryGroup6 : Subgroup SL(6, E) :=
  MonoidHom.eqLocus (sigmaA6 (involEquiv θ hθ)).toMonoidHom (MonoidHom.id _)

theorem mem_unitaryGroup6 {g : SL(6, E)} :
    g ∈ unitaryGroup6 θ hθ ↔ sigmaA6 (involEquiv θ hθ) g = g :=
  Iff.rfl

end Group

end CFSG.OddStandard.HigherRank.F3
