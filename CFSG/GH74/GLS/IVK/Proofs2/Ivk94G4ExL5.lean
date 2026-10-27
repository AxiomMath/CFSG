module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4E16
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] def diag5Vec (F : Type) [Field F] : Fin 4 → Fin 5 → F :=
  ![![-1, -1, 1, 1, 1], ![1, -1, -1, 1, 1], ![1, 1, -1, -1, 1], ![1, 1, 1, -1, -1]]

theorem diag5Vec_mul_self {F : Type} [Field F] (i : Fin 4) (j : Fin 5) :
    diag5Vec F i j * diag5Vec F i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [diag5Vec]

@[expose] def diag5GL (F : Type) [Field F] (i : Fin 4) : GL (Fin 5) F :=
  involGL (Matrix.diagonal (diag5Vec F i)) (by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun j => diag5Vec_mul_self i j))

theorem coe_diag5GL {F : Type} [Field F] (i : Fin 4) :
    ((diag5GL F i : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = Matrix.diagonal (diag5Vec F i) :=
  rfl

theorem det_diag5GL {F : Type} [Field F] (i : Fin 4) :
    ((diag5GL F i : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 := by
  rw [coe_diag5GL, Matrix.det_diagonal, Fin.prod_univ_five]
  fin_cases i <;> simp [diag5Vec]

theorem unitary_diag5GL {F : Type} [Field F] {q : ℕ} (hq : Odd q) (i : Fin 4) :
    (((diag5GL F i : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).map (· ^ q))ᵀ *
      ((diag5GL F i : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1 := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  rw [coe_diag5GL, Matrix.diagonal_map (by simp [hq0]), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  refine congrArg Matrix.diagonal (funext fun j => ?_)
  fin_cases i <;> fin_cases j <;> simp [diag5Vec, hq.neg_one_pow]

theorem coe_prod_diag5GL {F : Type} [Field F] (a : Fin 4 → ℕ) :
    (((List.ofFn fun i => diag5GL F i ^ a i).prod : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      Matrix.diagonal fun j => ∏ i, diag5Vec F i j ^ a i := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Units.val_mul, Units.val_pow_eq_pow_val, coe_diag5GL, Matrix.diagonal_pow,
    Matrix.diagonal_mul_diagonal, Fin.prod_univ_four, Pi.pow_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, mul_assoc]
  rfl

theorem prod_diag5GL_ne_scalar {F : Type} [Field F] (hne : (-1 : F) ≠ 1) (a : Fin 4 → Fin 2)
    (ha : a ≠ 0) (c : F) :
    (((List.ofFn fun i => diag5GL F i ^ (a i : ℕ)).prod : GL (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F) ≠ c • (1 : Matrix (Fin 5) (Fin 5) F) := by
  intro h
  rw [coe_prod_diag5GL, Matrix.smul_one_eq_diagonal] at h
  have h' := Matrix.diagonal_injective h
  have e0 := congrFun h' 0
  have e1 := congrFun h' 1
  have e2 := congrFun h' 2
  have e3 := congrFun h' 3
  have e4 := congrFun h' 4
  simp [Fin.prod_univ_four, diag5Vec] at e0 e1 e2 e3 e4
  have hx0 : (-1 : F) ^ (a 0 : ℕ) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have hx3 : (-1 : F) ^ (a 3 : ℕ) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have h1 : (-1 : F) ^ (a 1 : ℕ) = 1 := by
    refine mul_left_cancel₀ hx0 ?_
    rw [mul_one]
    exact e1.trans e0.symm
  have h2 : (-1 : F) ^ (a 2 : ℕ) = 1 := by
    refine mul_right_cancel₀ hx3 ?_
    rw [one_mul]
    exact e3.trans e4.symm
  have hc : c = 1 := by rw [← e2, h1, h2, mul_one]
  have h0 : (-1 : F) ^ (a 0 : ℕ) = 1 := e0.trans hc
  have h3 : (-1 : F) ^ (a 3 : ℕ) = 1 := e4.trans hc
  have key : ∀ k : Fin 2, (-1 : F) ^ (k : ℕ) = 1 → k = 0 := by
    intro k hk
    fin_cases k
    · rfl
    · exact (hne (by simpa using hk)).elim
  apply ha
  funext i
  fin_cases i
  · exact key _ h0
  · exact key _ h1
  · exact key _ h2
  · exact key _ h3

theorem exists_E16_diag5GL {F : Type} [Field F] (hne : (-1 : F) ≠ 1)
    {H : Subgroup (GL (Fin 5) F)} (hH : ∀ i, diag5GL F i ∈ H) :
    ∃ E : Subgroup (StatedProj H), (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  refine exists_E16_statedProj (diag5GL F) hH ?_ ?_ ?_
  · intro i
    refine ⟨1, ?_⟩
    rw [one_smul, coe_diag5GL, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun j => diag5Vec_mul_self i j)
  · intro i j
    refine ⟨1, ?_⟩
    rw [one_smul, coe_diag5GL, coe_diag5GL, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun k => mul_comm _ _)
  · exact fun a ha c => prod_diag5GL_ne_scalar hne a ha c

theorem k94_psl5 :
    K94Excl fun K _ => ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ LieModel K .PSL 5 p f := by
  refine k94Excl_of_E16 ?_
  rintro K _ _ ⟨p, f, -, -, h4, hL⟩
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hodd : Odd (Nat.card F) := by
    rw [hcard, Nat.odd_iff]
    omega
  refine exists_E16_of_equiv e
    (exists_E16_diag5GL (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i => ?_)
  exact Subgroup.subset_closure (det_diag5GL i)

theorem k94_psu5 :
    K94Excl fun K _ => ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ LieModel K .PSU 5 p f := by
  refine k94Excl_of_E16 ?_
  rintro K _ _ ⟨p, f, -, -, h4, hL⟩
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hq : Odd (p ^ f) := by
    rw [Nat.odd_iff]
    omega
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hq.pow
  refine exists_E16_of_equiv e
    (exists_E16_diag5GL (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i => ?_)
  exact Subgroup.subset_closure ⟨det_diag5GL i, unitary_diag5GL hq i⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
