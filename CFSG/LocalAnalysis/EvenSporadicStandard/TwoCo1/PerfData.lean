module

public import CFSG.Monster.VisQuot.Monomial

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot

@[expose] def perfPerm : Equiv.Perm (Fin 24) where
  toFun := ![15, 11, 13, 9, 14, 10, 12, 8, 7, 3, 5, 1, 6, 2, 4, 0, 23, 19, 21, 17, 22, 18, 20, 16]
  invFun := ![15, 11, 13, 9, 14, 10, 12, 8, 7, 3, 5, 1, 6, 2, 4, 0, 23, 19, 21, 17, 22, 18, 20, 16]
  left_inv := by decide
  right_inv := by decide

theorem perfPerm_inv : perfPerm⁻¹ = perfPerm := Equiv.ext fun i => by revert i; decide

theorem perfPerm_mul_self : perfPerm * perfPerm = 1 := Equiv.ext fun i => by revert i; decide

theorem perfPerm_basis : ∀ i, B i ∘ ⇑perfPerm ∈ C := by decide

theorem perfPerm_mem : perfPerm ∈ AutPerm :=
  mem_AutPerm_of_basis perfPerm_basis (by rw [perfPerm_inv]; exact perfPerm_basis)

@[expose] def perfAut : AutPerm := ⟨perfPerm, perfPerm_mem⟩

theorem perfAut_mul_self : perfAut * perfAut = 1 := Subtype.ext perfPerm_mul_self

@[expose] def perfWord : Fin 24 → ZMod 2 :=
  ![0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0]

theorem perfWord_mem : perfWord ∈ C := by decide

@[expose] def perfCode : C := ⟨perfWord, perfWord_mem⟩

theorem perfWord_add : ∀ i, perfWord i + permWord perfPerm perfWord i = 1 := by
  rw [permWord, perfPerm_inv]
  decide

theorem perfCode_add : perfCode + permC perfAut perfCode = ΩC :=
  Subtype.ext (funext fun i => perfWord_add i)

@[expose] def perfJ : latticeO := gO perfCode * PO perfAut

theorem permC_perfAut_symm : (permC perfAut).symm perfCode = permC perfAut perfCode := by
  rw [LinearEquiv.symm_apply_eq, ← permC_mul, perfAut_mul_self, permC_one]

theorem perfJ_mul_self : perfJ * perfJ = negOneO := by
  have h : perfCode + (permC perfAut).symm perfCode = ΩC := by
    rw [permC_perfAut_symm]
    exact perfCode_add
  calc perfJ * perfJ = gO perfCode * (PO perfAut * gO perfCode) * PO perfAut := by
        simp only [perfJ, mul_assoc]
    _ = gO (perfCode + (permC perfAut).symm perfCode) * PO (perfAut * perfAut) := by
        rw [PO_mul_gO, gO_add, PO_mul]
        simp only [mul_assoc]
    _ = negOneO := by rw [h, gO_ΩC, perfAut_mul_self, PO_one, mul_one]

end CFSG.EvenSporadicStandard.TwoCo1
