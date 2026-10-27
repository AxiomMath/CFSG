module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3M24
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3J2
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3J4
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3HS
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Ru
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3He
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.ComponentClassification.OuterAutomorphisms

theorem b3SporPair_rest_three
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) (hJ4 : J4ThreeCentralizerResidual) :
    ∀ name, B3SporRestPair name 3 → B3SporPair name 3 := by
  intro name h
  simp only [B3SporRestPair, true_and, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | h
  · exact b3SporPair_M11_three hbr hOut
  · exact b3SporPair_M12_three hbr hOut
  · exact b3SporPair_M22_three hbr hOut
  · exact b3SporPair_M23_three hbr hOut
  · exact b3SporPair_M24_three hbr hOut
  · exact b3SporPair_J2_three hbr hOut
  · exact b3SporPair_J4_three hOut hJ4
  · exact b3SporPair_HS_three hbr hOut
  · exact b3SporPair_Ru_three hbr hOut
  · exact b3SporPair_He_three hbr hOut
  · exfalso
    omega

end CFSG.HardMathSupport.Solomon.Coordinator
