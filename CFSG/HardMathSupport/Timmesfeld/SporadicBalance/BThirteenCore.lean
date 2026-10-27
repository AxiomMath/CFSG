module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] def BThirteenOddCore : Prop :=
  ∀ x : CFSG.Blueprint.NativeSporadic.B, orderOf x = 13 →
    ∀ K : Subgroup CFSG.Blueprint.NativeSporadic.B,
      K ≤ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.B) →
      (∀ g ∈ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.B), ∀ k ∈ K,
        g * k * g⁻¹ ∈ K) →
      Odd (Nat.card K) → ¬ 13 ∣ Nat.card K → K = ⊥

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
