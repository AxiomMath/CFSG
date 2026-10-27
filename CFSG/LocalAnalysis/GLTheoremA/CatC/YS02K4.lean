module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS02K1
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS02K3
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteB
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteM

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDSpor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Certs


theorem kdSporRow_B_K
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (p : ℕ) (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    KDSporRow .B p := by
  by_cases hs : KDSporRowLive .B p
  · rcases hs with h | ⟨-, h⟩
    · simp only [k2Spor] at h
      rcases h with rfl | rfl
      · exact CFSG.HardMathSupport.Dickson.BMRows.kdSporRow_B_three_of_kGroup
          (isKGroup_carrier_of_sporadic hbr _ hK)
      · exact CFSG.HardMathSupport.Dickson.BMRows.kdSporRow_B_five_of_kGroup
          (isKGroup_carrier_of_sporadic hbr _ hK)
    · rcases h with h | h <;> cases h
  · exact kdSporRow_of_not hs

theorem kdSporRow_M_K
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hM11 : KDSporRow .M 11) (hM13 : KDSporRow .M 13) (p : ℕ)
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    KDSporRow .M p := by
  by_cases hs : KDSporRowLive .M p
  · rcases hs with h | ⟨-, h⟩
    · simp only [k2Spor] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact CFSG.HardMathSupport.Dickson.BMRows.kdSporRow_M_three_of_kGroup
          (isKGroup_carrier_of_sporadic hbr _ hK)
      · exact CFSG.HardMathSupport.Dickson.BMRows.kdSporRow_M_five_of_kGroup
          (isKGroup_carrier_of_sporadic hbr _ hK)
      · exact CFSG.HardMathSupport.Dickson.BMRows.kdSporRow_M_seven
      · exact hM11
      · exact hM13
    · rcases h with h | h <;> cases h
  · exact kdSporRow_of_not hs

theorem kdLevelFiniteSporK_all
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hM11 : KDSporRow .M 11) (hM13 : KDSporRow .M 13) (p : ℕ) : KDLevelFiniteSporK p := by
  intro s hK
  by_cases hB : s = .B
  · subst hB
    exact kdSporRow_B_K hbr p hK
  by_cases hM : s = .M
  · subst hM
    exact kdSporRow_M_K hbr hM11 hM13 p hK
  exact kdSporRow_rest hOut hbr s hB hM p

end Certs

end CFSG.LocalAnalysis.GLTheoremA.KDSpor
