module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open CFSG.ComponentClassification

@[expose] def StdUHered : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → UHered G

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.uHered
    (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L) : UHered G := by
  haveI := h.simple
  exact UHered.of_simple hCU h.kProper (UGTAt.of_balanced h.oddCore)

theorem StdUHered.of_catalog (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) :
    StdUHered := by
  exact fun _ _ _ _ h => h.uHered hCU

end CFSG.EvenSporadicStandard.Induction.Balance
