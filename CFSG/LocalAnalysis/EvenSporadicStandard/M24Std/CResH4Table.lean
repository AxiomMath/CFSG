module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.M24Std

@[expose] def AutA6Table : Prop :=
  ∀ {K : Type} [Group K], K ≃* alternatingGroup (Fin 6) → ∀ α : MulAut K, α * α = 1 →
    Nat.card {k : K // α k = k} = 360 ∨ Nat.card {k : K // α k = k} = 8 ∨
      Nat.card {k : K // α k = k} = 24 ∨ Nat.card {k : K // α k = k} = 10

end CFSG.EvenSporadicStandard.M24Std
