module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Model
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Conf

public section

namespace CFSG.ComponentClassification.GSThmB

@[expose] def GS83Step12Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), Hyp52.L83Hyp h → h.IsQ3 →
    Eight.E32Conf X → False

end CFSG.ComponentClassification.GSThmB
