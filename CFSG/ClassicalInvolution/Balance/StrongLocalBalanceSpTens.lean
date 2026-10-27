module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpBasic

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {F : Type} [Field F]

@[expose] def tens (m n : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (m 0 0 • n) (m 0 1 • n) (m 1 0 • n) (m 1 1 • n)

theorem tens_mul (m m' n n' : Matrix (Fin 2) (Fin 2) F) :
    tens m n * tens m' n' = tens (m * m') (n * n') := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [tens, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

theorem tens_add_left (m m' n : Matrix (Fin 2) (Fin 2) F) :
    tens (m + m') n = tens m n + tens m' n := by
  simp only [tens, Matrix.fromBlocks_add, Matrix.add_apply, add_smul]

theorem tens_add_right (m n n' : Matrix (Fin 2) (Fin 2) F) :
    tens m (n + n') = tens m n + tens m n' := by
  simp only [tens, Matrix.fromBlocks_add, smul_add]

theorem tens_smul_left (c : F) (m n : Matrix (Fin 2) (Fin 2) F) :
    tens (c • m) n = c • tens m n := by
  simp only [tens, Matrix.smul_apply, smul_eq_mul, mul_smul, Matrix.fromBlocks_smul]

theorem tens_smul_right (c : F) (m n : Matrix (Fin 2) (Fin 2) F) :
    tens m (c • n) = c • tens m n := by
  simp only [tens, Matrix.fromBlocks_smul, smul_comm c]

theorem tens_transpose (m n : Matrix (Fin 2) (Fin 2) F) : (tens m n)ᵀ = tens mᵀ nᵀ := by
  simp only [tens, Matrix.fromBlocks_transpose, Matrix.transpose_smul, Matrix.transpose_apply]

theorem tens_one_one : tens (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [tens]

@[expose] def J0 : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

@[expose] def Rot : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0]

theorem Rot_transpose_mul_self : (Rot : Matrix (Fin 2) (Fin 2) F)ᵀ * Rot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rot, Matrix.mul_apply, Fin.sum_univ_two]

theorem Rot_mul_self : (Rot : Matrix (Fin 2) (Fin 2) F) * Rot = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rot, Matrix.mul_apply, Fin.sum_univ_two]

theorem gram_eq_tens : gram F 2 = tens (J0 : Matrix (Fin 2) (Fin 2) F) 1 := by
  simp only [gram, tens, J0]
  simp

theorem tens_one_Rot_symplectic :
    (tens 1 (Rot : Matrix (Fin 2) (Fin 2) F))ᵀ * gram F 2 * tens 1 Rot = gram F 2 := by
  rw [gram_eq_tens, tens_transpose, tens_mul, tens_mul]
  simp [Rot_transpose_mul_self]

@[expose] noncomputable def xSw : StatedSp 2 F :=
  ofSymplecticMat (tens 1 Rot) tens_one_Rot_symplectic

theorem mat_xSw : mat 2 F xSw = tens 1 Rot := rfl

theorem xSw_mul_self : (xSw : StatedSp 2 F) * xSw = negOne := by
  refine mat_injective ?_
  rw [map_mul, mat_xSw, tens_mul, mat_negOne, Rot_mul_self]
  simp only [one_mul]
  ext i j
  rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [tens, Matrix.neg_apply]

theorem tens_coeff {a a' b b' : Matrix (Fin 2) (Fin 2) F}
    (h : tens a 1 + tens b Rot = tens a' 1 + tens b' Rot) : a = a' ∧ b = b' := by
  have e := fun i j => congrFun (congrFun h i) j
  have e1 := e (Sum.inl 0) (Sum.inl 0)
  have e2 := e (Sum.inl 0) (Sum.inr 0)
  have e3 := e (Sum.inr 0) (Sum.inl 0)
  have e4 := e (Sum.inr 0) (Sum.inr 0)
  have e5 := e (Sum.inl 1) (Sum.inl 0)
  have e6 := e (Sum.inl 1) (Sum.inr 0)
  have e7 := e (Sum.inr 1) (Sum.inl 0)
  have e8 := e (Sum.inr 1) (Sum.inr 0)
  simp [tens, Rot] at e1 e2 e3 e4 e5 e6 e7 e8
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [e1, e2, e3, e4]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [e5, e6, e7, e8]

theorem exists_tens_of_commute {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : G * tens 1 Rot = tens 1 Rot * G) :
    ∃ m₀ m₁ : Matrix (Fin 2) (Fin 2) F, G = tens m₀ 1 + tens m₁ Rot := by
  have e := fun i j => congrFun (congrFun h i) j
  have k1 := e (Sum.inl 0) (Sum.inl 0)
  have k2 := e (Sum.inl 0) (Sum.inr 0)
  have k3 := e (Sum.inr 0) (Sum.inl 0)
  have k4 := e (Sum.inr 0) (Sum.inr 0)
  have k5 := e (Sum.inl 0) (Sum.inl 1)
  have k6 := e (Sum.inl 0) (Sum.inr 1)
  have k7 := e (Sum.inr 0) (Sum.inl 1)
  have k8 := e (Sum.inr 0) (Sum.inr 1)
  simp [tens, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Rot] at k1 k2 k3 k4 k5 k6 k7 k8
  refine ⟨!![G (Sum.inl 0) (Sum.inl 0), G (Sum.inl 0) (Sum.inr 0);
      G (Sum.inr 0) (Sum.inl 0), G (Sum.inr 0) (Sum.inr 0)],
    !![G (Sum.inl 1) (Sum.inl 0), G (Sum.inl 1) (Sum.inr 0);
      G (Sum.inr 1) (Sum.inl 0), G (Sum.inr 1) (Sum.inr 0)], ?_⟩
  ext i j
  rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [tens, Rot]
  all_goals first
    | exact k1 | exact k2 | exact k3 | exact k4 | exact k5.symm | exact k6.symm
    | exact k7.symm | exact k8.symm

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
