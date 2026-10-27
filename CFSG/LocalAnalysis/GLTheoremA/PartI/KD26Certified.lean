module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26Holds
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA


theorem sporadicOutOdd_holds : SporadicOutOdd := by
  intro S _ _ hS p hp hp2
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  cases i with
  | sporadic s =>
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s p hp hp2
  | cyclic _ _ => exact (hi : False).elim
  | alternating _ _ => exact (hi : False).elim
  | lie _ => exact (hi : False).elim

theorem kd26a_holds : KD26a :=
  kd26a_of_tables CFSG.HardMathSupport.Timmesfeld.DefChar.lieOuterRank_proved sporadicOutOdd_holds

end CFSG.LocalAnalysis.GLTheoremA
