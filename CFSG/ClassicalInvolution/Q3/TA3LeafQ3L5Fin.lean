module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open Matrix
open scoped MatrixGroups

abbrev x3M : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 1; 0, 1]

abbrev x3iM : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 2; 0, 1]

abbrev y3M : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 0; 1, 1]

theorem x3M_mul_x3iM : x3M * x3iM = 1 := by decide

theorem x3iM_mul_x3M : x3iM * x3M = 1 := by decide

@[expose] def X₃ : GL (Fin 2) (ZMod 3) := ⟨x3M, x3iM, x3M_mul_x3iM, x3iM_mul_x3M⟩

@[expose] def X₃s : SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨x3M, by decide⟩

@[expose] def Y₃s : SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨y3M, by decide⟩

theorem val_X₃ : (X₃ : Matrix (Fin 2) (Fin 2) (ZMod 3)) = x3M := rfl

theorem val_X₃_inv : ((X₃⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = x3iM :=
  rfl

theorem X₃_pow_three : X₃ ^ 3 = 1 := Units.ext (by
  rw [Units.val_pow_eq_pow_val, Units.val_one, val_X₃]
  decide)

theorem X₃_neg_pow_three : (X₃ * -1) ^ 3 ≠ 1 := fun h => by
  have := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_neg, Units.val_one, val_X₃] at this
  revert this
  decide

theorem mat_not_comm : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), M * M * (M * M) = 1 →
    M * M ≠ 1 → x3M * M ≠ M * x3M := by
  decide

set_option maxRecDepth 100000 in
theorem mat_comm_q8 : ∀ M A : Matrix (Fin 2) (Fin 2) (ZMod 3), M * M * (M * M) = 1 →
    M * M ≠ 1 → A * M = M * A → A * (x3M * M * x3iM) = x3M * M * x3iM * A →
      A = 0 ∨ A = 1 ∨ A = -1 := by
  decide

theorem mat_comm_sl2 : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3), A * x3M = x3M * A →
    A * y3M = y3M * A → A = 0 ∨ A = 1 ∨ A = -1 := by
  decide

theorem val_of_orderOf_four {S : GL (Fin 2) (ZMod 3)} (hS : orderOf S = 4) :
    (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) * S * (S * S) = 1 ∧
      (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) * S ≠ 1 := by
  have h4 : S ^ 4 = 1 := by rw [← hS]; exact pow_orderOf_eq_one S
  have h2 : S ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hS] at this
    norm_num at this
  refine ⟨?_, fun h => h2 (Units.ext ?_)⟩
  · have := congrArg Units.val h4
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [← this, ← mul_assoc, pow_succ, pow_succ, pow_succ, pow_one]
  · rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    exact h

theorem eq_or_of_val {A : GL (Fin 2) (ZMod 3)}
    (h : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 0 ∨ (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
      (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1) : A = 1 ∨ A = -1 := by
  rcases h with h | h | h
  · exact absurd h A.ne_zero
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h]; rfl))

theorem not_comm_X₃ {S : GL (Fin 2) (ZMod 3)} (hS : orderOf S = 4) : X₃ * S ≠ S * X₃ :=
  fun h => by
    obtain ⟨h4, h2⟩ := val_of_orderOf_four hS
    have := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, val_X₃] at this
    exact mat_not_comm _ h4 h2 this

theorem eq_or_of_comm_q8 {S A : GL (Fin 2) (ZMod 3)} (hS : orderOf S = 4) (h1 : A * S = S * A)
    (h2 : A * (X₃ * S * X₃⁻¹) = X₃ * S * X₃⁻¹ * A) : A = 1 ∨ A = -1 := by
  obtain ⟨h4, h2'⟩ := val_of_orderOf_four hS
  have e1 := congrArg Units.val h1
  have e2 := congrArg Units.val h2
  rw [Units.val_mul, Units.val_mul] at e1
  simp only [Units.val_mul, val_X₃, val_X₃_inv] at e2
  exact eq_or_of_val (mat_comm_q8 _ _ h4 h2' e1 e2)

theorem eq_or_of_comm_sl2 {A : GL (Fin 2) (ZMod 3)}
    (h : ∀ B : SpecialLinearGroup (Fin 2) (ZMod 3), A * B.toGL = B.toGL * A) :
    A = 1 ∨ A = -1 := by
  have e1 := congrArg Units.val (h X₃s)
  have e2 := congrArg Units.val (h Y₃s)
  rw [Units.val_mul, Units.val_mul] at e1 e2
  exact eq_or_of_val (mat_comm_sl2 _ e1 e2)

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5
