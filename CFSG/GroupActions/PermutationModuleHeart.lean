module

public import CFSG.GroupActions.PrimitiveNormal
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupActions

open MulAction

variable {Ω : Type*} {p : ℕ}

@[expose] def permFun (g : Equiv.Perm Ω) : (Ω → ZMod p) →ₗ[ZMod p] (Ω → ZMod p) where
  toFun f x := f (g⁻¹ x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem permFun_apply (g : Equiv.Perm Ω) (f : Ω → ZMod p) (x : Ω) :
    permFun g f x = f (g⁻¹ x) :=
  rfl

end CFSG.GroupActions
