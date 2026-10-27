module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def TwoNilp (D : Type) [Group D] : Prop :=
  ∃ N : Subgroup D, N.Normal ∧ Odd (Nat.card ↥N) ∧ ∃ a : ℕ, N.index = 2 ^ a

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
