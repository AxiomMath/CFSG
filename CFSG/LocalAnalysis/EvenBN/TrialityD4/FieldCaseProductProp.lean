module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseInvolution

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

@[expose] def TrialityD4ProductFieldCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)), 2 ≤ f → h.LayerHyp d → ¬ LayerHypFieldAlt h d → False

end CFSG.LocalAnalysis.EvenBN.TrialityD4
