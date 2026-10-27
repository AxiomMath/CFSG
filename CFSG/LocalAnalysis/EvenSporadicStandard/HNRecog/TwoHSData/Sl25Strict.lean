module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Matrix

abbrev SL25 : Type := SpecialLinearGroup (Fin 2) (ZMod 5)

@[expose] def sl25Norm (A : SL25) : SL25 :=
  ⟨!![A.1 0 0, A.1 0 1; A.1 1 0, A.1 1 1], by
    rw [Matrix.det_fin_two_of, ← Matrix.det_fin_two]
    exact A.2⟩

theorem sl25Norm_eq (A : SL25) : sl25Norm A = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

structure SL25S where
  val : SL25
  deriving DecidableEq

namespace SL25S

@[ext] theorem ext {A B : SL25S} (h : A.val = B.val) : A = B := by
  cases A; cases B; cases h; rfl

instance : Mul SL25S := ⟨fun A B => ⟨sl25Norm (A.val * B.val)⟩⟩

instance : One SL25S := ⟨⟨1⟩⟩

instance : Inv SL25S := ⟨fun A => ⟨A.val⁻¹⟩⟩

theorem val_mul (A B : SL25S) : (A * B).val = A.val * B.val := sl25Norm_eq _

theorem val_one : (1 : SL25S).val = 1 := rfl

theorem val_inv (A : SL25S) : A⁻¹.val = A.val⁻¹ := rfl

instance : Group SL25S :=
  Group.ofLeftAxioms
    (fun a b c => ext (by simp only [val_mul, mul_assoc]))
    (fun a => ext (by simp only [val_mul, val_one, one_mul]))
    (fun a => ext (by simp only [val_mul, val_inv, val_one, inv_mul_cancel]))

def mulEquiv : SL25S ≃* SL25 where
  toFun := SL25S.val
  invFun := SL25S.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' A B := val_mul A B

end SL25S

theorem card_SL25S : Nat.card SL25S = 120 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.card_congr SL25S.mulEquiv.toEquiv]
  refine (Matrix.card_SL_field 2 (𝔽 := ZMod 5)).trans ?_
  simp [Fin.prod_univ_two, ZMod.card]

end CFSG.EvenSporadicStandard.HNRecog
