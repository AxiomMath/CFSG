module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporOne
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClose
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3He
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestHe
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestHeTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestFi23
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestFi24
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestTh
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestM
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveJ2
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveHSMcL
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveSuz
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveCo3
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestRu
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestON
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestJ4

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance


theorem b3SporPair_monsterSection_of (hB7 : B3SporPair .B 7) :
    ∀ p : ℕ, p.Prime → ∀ name ∈ ({.He, .HN, .Th, .Fi22, .Fi23, .Fi24Prime, .B, .M} :
      Finset TauCeti.SporadicName), (p ≠ 2 ∨ name = .He) → B3SporPair name p := by
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro p hp name hname hp2
  by_cases h2p : p = 2
  · subst h2p
    rcases hp2 with h | h
    · exact absurd rfl h
    · subst h; exact b3SporPair_He_two hbr
  by_cases h2 : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic name).Group
  · rcases sporadicP2Table_holds name p hp h2p h2 with h | h
    · exact b3SporPair_of_sporadicOPrimeHolds hp h2p hbr hOut
        (sporadicOPrime_of_parts (sporadicOneParts_of_open
            CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.bThreeRc_holds
            CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.bThreeRd_holds
            CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bFiveNonCentral_holds
            CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.twoAPureKlein_three_Gmat
            CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.twoATwoCommuting_five_Gmat
            CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus.monsterSevenClasses)
          name p h)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hname
      unfold B3SporRestPair at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
        rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [reduceCtorEq, false_or, or_false, or_self] at h <;>
        first
          | exact b3SporPair_He_three hbr hOut
          | exact b3SporPair_He_five hbr hOut
          | exact b3SporPair_He_seven hbr hOut
          | exact b3SporPair_Fi22_five hbr hOut
          | exact b3SporPair_Fi23_five hbr hOut
          | exact b3SporPair_Fi24Prime_five hbr hOut
          | exact b3SporPair_Fi24Prime_seven hbr hOut
          | exact b3SporPair_Th_five hbr hOut
          | exact b3SporPair_Th_seven hbr hOut
          | exact hB7
          | exact b3SporPair_M_eleven hbr hOut
          | exact b3SporPair_M_thirteen hbr hOut
  · refine b3SporPair_of_card_exact hp h2p hOut fun S _ _ he => ?_
    rw [Nat.card_congr he.some.toEquiv]
    exact h2

theorem b3SporRestPairs_of (hB7 : B3SporPair .B 7) :
    ∀ (name : TauCeti.SporadicName) (p : ℕ), B3SporRestPair name p → p ≠ 3 →
      B3SporPair name p := by
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro name p h hp3
  unfold B3SporRestPair at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl⟩
  · exact absurd rfl hp3
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact b3SporPair_J2_five hbr hOut
    · exact b3SporPair_HS_five hbr hOut
    · exact b3SporPair_McL_five hbr hOut
    · exact b3SporPair_Suz_five hbr hOut
    · exact b3SporPair_He_five hbr hOut
    · exact b3SporPair_Ru_five hbr hOut
    · exact b3SporPair_of_sporadicOPrimeHolds (by norm_num) (by norm_num) hbr hOut
        sporadicOPrimeHolds_Co2_five
    · exact b3SporPair_Co3_five hbr hOut
    · exact b3SporPair_Fi22_five hbr hOut
    · exact b3SporPair_Fi23_five hbr hOut
    · exact b3SporPair_Fi24Prime_five hbr hOut
    · exact b3SporPair_Th_five hbr hOut
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact b3SporPair_He_seven hbr hOut
    · exact b3SporPair_ONan_seven hbr hOut
    · exact b3SporPair_of_sporadicOPrimeHolds (by norm_num) (by norm_num) hbr hOut
        sporadicOPrimeHolds_Co1_seven
    · exact b3SporPair_Fi24Prime_seven hbr hOut
    · exact b3SporPair_Th_seven hbr hOut
    · exact hB7
  · rcases h with rfl | rfl
    · exact b3SporPair_J4_eleven hbr hOut
    · exact b3SporPair_M_eleven hbr hOut
  · exact b3SporPair_M_thirteen hbr hOut

end CFSG.HardMathSupport.Solomon.Coordinator
