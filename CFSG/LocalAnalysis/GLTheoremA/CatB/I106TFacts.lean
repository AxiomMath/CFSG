module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open

@[expose] def I106TE27Fact : Prop :=
  ∀ (i : TauCeti.CFSGIndex) (H : Type) [Group H] [Finite H],
    isType1430 i → ¬ isSp48 i → CFSG.Open.IsQuasisimple H →
    (∀ z ∈ Subgroup.center H, ∃ n : ℕ, z ^ 3 ^ n = 1) →
    Nonempty (H ⧸ Subgroup.center H ≃* i.Group) →
    ∃ E : Subgroup H, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ E ⊓ Subgroup.center H = ⊥

@[expose] def I106TSp48Fact : Prop :=
  ∀ (i : TauCeti.CFSGIndex) (H : Type) [Group H] [Finite H],
    isSp48 i → CFSG.Open.IsQuasisimple H →
    (∀ z ∈ Subgroup.center H, ∃ n : ℕ, z ^ 3 ^ n = 1) →
    Nonempty (H ⧸ Subgroup.center H ≃* i.Group) →
    ∀ α : H ≃* H, (∀ x, α (α (α x)) = x) → (¬ ∃ h : H, ∀ x, α x = h * x * h⁻¹) →
    ∃ E : Subgroup H, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      (∀ e ∈ E, α e = e) ∧ E ⊓ Subgroup.center H = ⊥

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
