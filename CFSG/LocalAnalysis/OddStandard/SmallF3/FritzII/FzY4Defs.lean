module

public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

abbrev FzZ244 : Type := Multiplicative (ZMod 2 × ZMod 4 × ZMod 4)

abbrev FzSigma4 : Type := Equiv.Perm (Fin 4)

abbrev FzZ2xSigma4 : Type := Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)

end CFSG.OddStandard.SmallF3.FritzII
