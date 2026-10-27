module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1CenterNine
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuterAux
public import CFSG.Milestones.FAM_M_simplicity

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem SporadicMultD1.card_outer_sporadic_dvd_two
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (s : TauCeti.SporadicName) :
    Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) ∣ 2 := by
  obtain ⟨e⟩ := hbr s
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact card_outer_carrier_dvd_two CFSG.Milestones.fam_m_simplicity s

theorem kFactCompCenterNine_of_griess
    (hGA : GriessMultipliersAllModels)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group)) :
    KFactCompCenterNine :=
  kFactCompCenterNine_of_outer hGA (SporadicMultD1.card_outer_sporadic_dvd_two hbr)

end CFSG.AGLEmbedding
