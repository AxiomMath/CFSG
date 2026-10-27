module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Assembly.LowTwoRank

@[expose] def D4OuterExport : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {ℓ f : ℕ}, StatedClassicalModel G .POmegaPlus 4 ℓ f →
    ∀ β : MulAut G, β ^ 3 = 1 → (∀ a : G, MulAut.conj a ≠ β) →
      LieCompExport ℓ β ∨ NoThreeComponents β

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
