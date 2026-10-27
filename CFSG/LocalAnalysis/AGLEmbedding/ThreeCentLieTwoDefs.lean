module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def KFactThreeCentTrialityTwo : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .D 4 q) →
    ∀ α : MulAut (TauCeti.CFSGIndex.lie d).Group, α ∉ inner (TauCeti.CFSGIndex.lie d).Group →
      α ^ 3 = 1 →
      (∀ Q : Subgroup (TauCeti.CFSGIndex.lie d).Group, ⁅Q, Q⁆ = Q → (∀ y ∈ Q, α y = y) →
        Q = ⊥) →
      ∀ x : (TauCeti.CFSGIndex.lie d).Group,
        x⁻¹ * α x ∈ Subgroup.center (TauCeti.CFSGIndex.lie d).Group → ∀ n : ℕ,
          Nat.Coprime 6 n → x ^ n ∈ Subgroup.center (TauCeti.CFSGIndex.lie d).Group →
            x ∈ Subgroup.center (TauCeti.CFSGIndex.lie d).Group

end CFSG.AGLEmbedding
