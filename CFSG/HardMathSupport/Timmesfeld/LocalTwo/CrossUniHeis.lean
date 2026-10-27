module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUni
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniHeisSplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem uniHeisenbergPlaneBalance_holds : UniHeisenbergPlaneBalance := by
  intro ℓ f n K _ h hn hne p hp hp5 hpℓ hpq hpn hnp A B c hc1 hcp hAB hAp hBp hA1 hBA H hH _hN
  have hp2 : p ≠ 2 := by omega
  have hq3 : 3 < ℓ ^ f := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  have hn2p : 2 * p ≤ n := by
    obtain ⟨s, hs⟩ := hpn
    have hs0 : s ≠ 0 := by rintro rfl; omega
    have hs1 : s ≠ 1 := by rintro rfl; omega
    have : 2 ≤ s := by omega
    rw [hs]
    nlinarith
  obtain ⟨A0, B0, c', hc'1, hc'p, hAB', hA0p, hA01, hA0E, hB0E⟩ :=
    exists_split_heis_pair hn hne hp hp2 hpq hc1 hcp hAB hAp hBp hA1 hBA
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_localDeltaIn_heis hn hne hq3 hp hp2 hpq hn2p hc'1 hc'p hAB' hA0p hA01 hH
    hA0E hB0E hg

theorem crossCharTwoFamCat_twistedA : CrossCharTwoFamCat .twistedA :=
  crossCharTwoFamCat_twistedA_of_heisenberg uniHeisenbergPlaneBalance_holds

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
