module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def SolomonAltOutcome (G : Type) [Group G] (A : Subgroup G) (n : ℕ) : Prop :=
  (∃ K₁ K₂ : Subgroup G, K₁.IsSubnormal ∧ K₂.IsSubnormal ∧
      Nonempty (K₁ ⧸ center K₁ ≃* alternatingGroup (Fin n)) ∧
      Nonempty (K₂ ⧸ center K₂ ≃* alternatingGroup (Fin n)) ∧
      A ≤ K₁ ⊔ K₂ ∧ (K₁ ⊔ K₂).Normal) ∨
    Nonempty (G ≃* Equiv.Perm (Fin (n + 2))) ∨
    (n = 11 ∧ IsSporadic G .Ly) ∨
    (n = 10 ∧ (commutator G).index = 2) ∨
    (n = 8 ∧ IsSporadic (commutator G) .McL) ∨
    (n = 8 ∧ IsSporadic (commutator G) .HS ∧ (commutator G).index = 2) ∨
    (n = 8 ∧ LieModel (commutator G) .PSL 4 2 2)

end CFSG.OddStandard
