module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuterAux
public import CFSG.Milestones.FAM_M_simplicity

public section

namespace CFSG.AGLEmbedding


theorem not_dvd_card_outer_sporadic
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group)) :
    ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (TauCeti.CFSGIndex.sporadic s).Group) :=
  not_dvd_card_outer_sporadic_of hbr CFSG.Milestones.fam_m_simplicity

end CFSG.AGLEmbedding
