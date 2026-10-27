module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Co1

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def NoOrderSixtyFiveBM : Prop :=
  ∀ s : TauCeti.SporadicName, (s = .B ∨ s = .M) → NoOrderSixtyFiveAt s

section Co1

theorem noOrderSixtyFive_of_BM
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h : NoOrderSixtyFiveBM) : NoOrderSixtyFive := by
  intro s hs
  rcases hs with rfl | hs
  · exact noOrderSixtyFiveAt_Co1 (hbr .Co1)
  · exact h s hs

end Co1

end CFSG.HardMathSupport.Solomon.Coordinator
