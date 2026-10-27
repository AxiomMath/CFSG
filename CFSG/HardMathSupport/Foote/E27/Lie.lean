module

public import CFSG.HardMathSupport.Foote.E27.Defs

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Open

@[expose] def E27LieIn : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X), E27Config X K R T z → z ∈ K →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → False

@[expose] def E27LieOut : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X), E27Config X K R T z → z ∉ K →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → False

theorem e27LieSlice_of_in_out (hIn : E27LieIn) (hOut : E27LieOut) : E27LieSlice := by
  intro X _ _ K R T z hc d he
  by_cases hz : z ∈ K
  · exact hIn X K R T z hc hz d he
  · exact hOut X K R T z hc hz d he

@[expose] def E27LieOuterAut : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → 3 ^ 5 ∣ Nat.card (MulAut K) →
    ∀ u : MulAut K, u ^ 3 = 1 → (∀ k : K, u ≠ MulAut.conj k) →
    (∀ D : Subgroup K, (∀ x ∈ D, u x = x) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D) →
    (∀ Q : Subgroup K, (∀ x ∈ Q, u x = x) → IsPGroup 3 Q → Nat.card Q ≤ 9) →
    (∃ T : Subgroup K, (∀ x ∈ T, u x = x) ∧ IsElemAbelian 3 T ∧ Nat.card T = 9) → False

end CFSG.HardMathSupport.Foote.E27
