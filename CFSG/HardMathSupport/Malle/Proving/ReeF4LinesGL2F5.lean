module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Malle.Proving

open scoped Matrix

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev Vec5 : Type := Fin 2 → ZMod 5

end CFSG.HardMathSupport.Malle.Proving
