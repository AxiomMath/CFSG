module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

@[expose] def SLFactorFacts : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (m : ℕ), 2 ≤ m → (m = 2 → 4 ≤ Fintype.card E) →
    LieFactorData (ringChar E) (Matrix.SpecialLinearGroup (Fin m) E)

@[expose] def SLAltSixFacts : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (m : ℕ), 2 ≤ m →
    Nonempty ((Matrix.SpecialLinearGroup (Fin m) E ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) ≃* alternatingGroup (Fin 6)) →
      m = 2 ∧ Fintype.card E = 9

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
