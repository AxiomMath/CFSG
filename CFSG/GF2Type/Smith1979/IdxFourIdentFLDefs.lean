
module

public import CFSG.GF2Type.Smith1979.IdxFourIdentFLData
public import CFSG.GF2Type.Smith1979.IdxFourModelDefs
public import CFSG.GF2Type.Smith1979.IdxFourIdentMonDefs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem uRows_inv (a b : Fin 4) :
    mulR (uRowsTable[4 * (a : ℕ) + (b : ℕ)]!) (uInvRowsTable[4 * (a : ℕ) + (b : ℕ)]!) = idR ∧
      mulR (uInvRowsTable[4 * (a : ℕ) + (b : ℕ)]!) (uRowsTable[4 * (a : ℕ) + (b : ℕ)]!) = idR := by
  revert a b
  decide +kernel

@[expose] noncomputable def Umat (a b : Fin 4) : G12 :=
  Viol.eqvOf (uRowsTable[4 * (a : ℕ) + (b : ℕ)]!) (uInvRowsTable[4 * (a : ℕ) + (b : ℕ)]!)
    (uRows_inv a b).1 (uRows_inv a b).2

theorem Umat_apply (a b : Fin 4) (x : V12) :
    Umat a b x = linOfRows (uRowsTable[4 * (a : ℕ) + (b : ℕ)]!) x := rfl

@[expose] def Delta0 (s : ZMod 3) : G12 := diagE (fun i => if i = 0 then s else 0)

@[expose] def chStd : Fin 6 → ZMod 3 := fun i => if (i : ℕ) < 3 then 1 else 0

theorem y3_inv : mulR y3RowsData y3InvRowsData = idR ∧ mulR y3InvRowsData y3RowsData = idR := by
  decide +kernel

theorem y3RowsData_eq : y3RowsData = y3Rows := by decide +kernel

@[expose] noncomputable def y3e : G12 := Viol.eqvOf y3RowsData y3InvRowsData y3_inv.1 y3_inv.2

theorem y3e_apply (x : V12) : y3e x = linOfRows y3Rows x := by
  rw [← y3RowsData_eq]; rfl

end CFSG.GF2Type.Smith1979.IdxFour
