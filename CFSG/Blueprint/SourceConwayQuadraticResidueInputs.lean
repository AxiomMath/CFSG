module

public import CFSG.Blueprint.SourceBinaryGolayCode
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Blueprint.EvenSource

open Matrix

instance fact_prime_twentyThree : Fact (Nat.Prime 23) := ⟨by decide⟩

end CFSG.Blueprint.EvenSource
