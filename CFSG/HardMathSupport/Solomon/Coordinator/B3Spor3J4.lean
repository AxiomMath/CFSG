module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def J4ThreeCentralizerResidual : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .J4).Group) →
      ∀ s : S, orderOf s = 3 → ∀ o ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set S)),
        ∀ c ∈ Subgroup.centralizer ({s} : Set S), o * c = c * o

theorem b3SporPair_J4_three (hOut : SporadicOuterLeTwo) (hres : J4ThreeCentralizerResidual) :
    B3SporPair .J4 3 := by
  refine b3SporPair_of_centralizer_phi Nat.prime_three (by norm_num) hOut ?_
  intro S _ _ _ he s hs
  refine b3Phi_of_comm fun J hJ g hg o ho => ?_
  exact hres S he s hs o ho g (hJ.1 hg)

end CFSG.HardMathSupport.Solomon.Coordinator
