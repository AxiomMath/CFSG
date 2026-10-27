module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuterAux
public import CFSG.Milestones.FAM_M_simplicity
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

theorem sporadicOuterLeTwo_holds
    : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo := by
  intro S _ _ _ _ name he
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group name
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (CFSG.Blueprint.NativeSporadic.Carrier name)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (e.trans e'.symm)).toEquiv
  rw [hcard]
  exact Nat.le_of_dvd (by norm_num)
    (CFSG.AGLEmbedding.card_outer_carrier_dvd_two CFSG.Milestones.fam_m_simplicity name)

end CFSG.HardMathSupport.Timmesfeld.Proving

end
