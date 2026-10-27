module

public import Mathlib.Data.Nat.Factorization.Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

@[expose] def nuQ (q : ℕ) : ℕ := ((q * (q ^ 2 - 1)) ^ 2 / 2).factorization 2

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
