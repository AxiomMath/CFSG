module

public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadicReps

public section

namespace CFSG.Blueprint

@[expose] def NativeCatalog (G : Type) [Group G] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    Milestones.ClassicalRep G ∨ ExceptionalRep G ∨ NativeSporadic.NativeSporadicRep G

end CFSG.Blueprint
