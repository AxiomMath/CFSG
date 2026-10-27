module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.CGT.T75P

open scoped MatrixGroups Matrix

variable {F : Type} [Field F]

@[expose] def a8xUT (a b c : F) : SL(3, F) :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem a8xUT_apply (a b c : F) :
    ((a8xUT a b c : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, a, c; 0, 1, b; 0, 0, 1] := rfl

theorem a8xUT_zero : a8xUT (0 : F) 0 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a8xUT_apply]

theorem a8xUT_mul (a b c a' b' c' : F) :
    a8xUT a b c * a8xUT a' b' c' = a8xUT (a + a') (b + b') (c + c' + a * b') := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a8xUT_apply, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem a8xUT_inv (a b c : F) : (a8xUT a b c)⁻¹ = a8xUT (-a) (-b) (a * b - c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [a8xUT_mul, ← a8xUT_zero]
  congr 1 <;> ring

theorem a8xUT_injective : Function.Injective fun p : F × F × F => a8xUT p.1 p.2.1 p.2.2 := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h01 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 1) h
  have h12 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 1 2) h
  have h02 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 2) h
  simp only [a8xUT_apply, Matrix.of_apply] at h01 h12 h02
  simp_all

variable (F) in
@[expose] def a8xU : Subgroup SL(3, F) where
  carrier := Set.range fun p : F × F × F => a8xUT p.1 p.2.1 p.2.2
  one_mem' := ⟨(0, 0, 0), a8xUT_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, b, c⟩, rfl⟩ ⟨⟨a', b', c'⟩, rfl⟩
    exact ⟨(a + a', b + b', c + c' + a * b'), (a8xUT_mul a b c a' b' c').symm⟩
  inv_mem' := by
    rintro _ ⟨⟨a, b, c⟩, rfl⟩
    exact ⟨(-a, -b, a * b - c), (a8xUT_inv a b c).symm⟩

theorem a8xUT_mem (a b c : F) : a8xUT a b c ∈ a8xU F := ⟨(a, b, c), rfl⟩

theorem a8xU_card : Nat.card (a8xU F) = Nat.card F ^ 3 := by
  have h : Nat.card (a8xU F) = Nat.card (F × F × F) :=
    Nat.card_range_of_injective (a8xUT_injective (F := F))
  rw [h, Nat.card_prod, Nat.card_prod]
  ring

end CFSG.CGT.T75P
