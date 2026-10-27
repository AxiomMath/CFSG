module

public import CFSG.GF2Type.Smith1979.GammaU.EnumDefs
public import CFSG.Monster.B.Co2.BFS
public import Certificates.Data.CFSGNative.Schreier.Check
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

namespace Chain

@[expose] noncomputable def codePerm (U : V12 ≃ₗ[ZMod 2] V12) : Equiv.Perm (Fin 4096) where
  toFun n := ⟨codeOf (U (vecOf n)), codeOf_lt _⟩
  invFun n := ⟨codeOf (U.symm (vecOf n)), codeOf_lt _⟩
  left_inv n := Fin.ext (by
    simp only [vecOf_codeOf, LinearEquiv.symm_apply_apply]
    exact codeOf_vecOf n.2)
  right_inv n := Fin.ext (by
    simp only [vecOf_codeOf, LinearEquiv.apply_symm_apply]
    exact codeOf_vecOf n.2)

theorem codePerm_apply (U : V12 ≃ₗ[ZMod 2] V12) (n : Fin 4096) :
    ((codePerm U n : Fin 4096) : ℕ) = codeOf (U (vecOf n)) := rfl

end Chain

end CFSG.GF2Type.Smith1979.IdxFour
