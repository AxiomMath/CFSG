module

public import CFSG.HardMathSupport.Foote.E27.Lie

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Open TauCeti

@[expose] def E27LieOuterAutAt (P : LieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : ValidLieTypeIndex), P d.1 →
    Nonempty (K ≃* (CFSGIndex.lie d).Group) → 3 ^ 5 ∣ Nat.card (MulAut K) →
    ∀ u : MulAut K, u ^ 3 = 1 → (∀ k : K, u ≠ MulAut.conj k) →
    (∀ D : Subgroup K, (∀ x ∈ D, u x = x) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D) →
    (∀ Q : Subgroup K, (∀ x ∈ Q, u x = x) → IsPGroup 3 Q → Nat.card Q ≤ 9) →
    (∃ T : Subgroup K, (∀ x ∈ T, u x = x) ∧ IsElemAbelian 3 T ∧ Nat.card T = 9) → False

theorem e27LieOuterAut_of_all (h : E27LieOuterAutAt (fun _ => True)) :
    CFSG.HardMathSupport.Foote.E27.E27LieOuterAut :=
  fun K _ _ d e => h K d trivial e

end CFSG.HardMathSupport.Malle.E27Lie
