module

public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestJ4
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestRu
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestON
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Ru
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Assemble
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyFive

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance


theorem b3SporPair_pariah :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ name ∈ ({.J1, .J3, .J4, .ONan, .Ly, .Ru} :
      Finset TauCeti.SporadicName), B3SporPair name p := by
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro p hp hp2 name hname
  by_cases h2 : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic name).Group
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hname
    rcases sporadicP2Table_holds name p hp hp2 h2 with h | h
    · refine b3SporPair_of_sporadicOPrimeHolds hp hp2 hbr hOut ?_
      unfold SporadicOnePair at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl⟩
      · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [reduceCtorEq, false_or, or_false, or_self] at h
        · exact (sporadicOnePairHolds_J3 (hbr .J3)).1
        · exact sporadicOPrimeHolds_ONan_three
        · exact sporadicOPrimeHolds_Ly_three
      · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [reduceCtorEq, false_or, or_false, or_self] at h
        exact sporadicOPrimeHolds_Ly_five
      · rcases hname with h | h | h | h | h | h <;> cases h
    · unfold B3SporRestPair at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
      · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [reduceCtorEq, false_or, or_false, or_self] at h
        · exact b3SporPair_J4_three_of_bridges hbr hOut
        · exact b3SporPair_Ru_three hbr hOut
      · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [reduceCtorEq, false_or, or_false, or_self] at h
        exact b3SporPair_Ru_five hbr hOut
      · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [reduceCtorEq, false_or, or_false, or_self] at h
        exact b3SporPair_ONan_seven hbr hOut
      · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [reduceCtorEq, false_or, or_false, or_self] at h
        exact b3SporPair_J4_eleven hbr hOut
      · rcases hname with h' | h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  · refine b3SporPair_of_card_exact hp hp2 hOut fun S _ _ he => ?_
    rw [Nat.card_congr he.some.toEquiv]
    exact h2

end CFSG.HardMathSupport.Solomon.Coordinator
