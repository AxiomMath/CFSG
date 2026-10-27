module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporTh5
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24Seven
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Minus
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDL227
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHN

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDSpor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Certs

theorem kdSporRow_rest (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (s : TauCeti.SporadicName) (hB : s ≠ .B) (hM : s ≠ .M) (p : ℕ) : KDSporRow s p := by
  by_cases hs : KDSporRowLive s p
  · rcases hs with h | ⟨rfl, h | h⟩
    · cases s
      all_goals simp only [k2Spor] at h
      case M11 => subst h; exact kdSporRow_M11_three hOut
      case M12 => subst h; exact kdSporRow_M12_eleven hOut
      case J3 => subst h; exact kdSporRow_J3_three hOut hbr
      case J4 => subst h; exact kdSporRow_J4_eleven hbr hOut
      case HS => subst h; exact kdSporRow_HS_five hOut hbr
      case McL =>
        rcases h with rfl | rfl
        · exact kdSporRow_McL_three hOut hbr
        · exact kdSporRow_McL_five hOut hbr
      case He => subst h; exact He7.kdSporRow_He_seven hOut hbr
      case Ru => subst h; exact kdSporRow_Ru_five hOut hbr
      case Suz =>
        subst h; exact CFSG.HardMathSupport.Dickson.I271.KDLevelSuz.kdSporRow_Suz_three hOut hbr
      case ONan =>
        rcases h with rfl | rfl
        · exact kdSporRow_ON_three hOut hbr
        · exact kdSporRow_ON_seven hOut
      case Co2 =>
        subst h; exact CFSG.HardMathSupport.Dickson.I271.KDLevelCo2.kdSporRow_Co2_three hOut hbr
      case Co3 =>
        subst h; exact CFSG.HardMathSupport.Dickson.I271.KDLevelCo3.kdSporRow_Co3_three hOut hbr
      case Fi22 =>
        subst h; exact CFSG.HardMathSupport.Dickson.I271.KDLevelFi22.kdSporRow_Fi22_three hOut hbr
      case Fi23 =>
        subst h; exact CFSG.HardMathSupport.Dickson.I271.KDLevelFi23.kdSporRow_Fi23_three hOut hbr
      case Fi24Prime =>
        rcases h with rfl | rfl
        · exact CFSG.HardMathSupport.Dickson.I271.TabFi24.kdSporRow_Fi24_three hOut hbr
        · exact Fi24Seven.kdSporRow_Fi24_seven hOut hbr
      case HN => subst h; exact kdSporRow_HN_five hOut hbr
      case Ly =>
        rcases h with rfl | rfl
        · exact kdSporRow_Ly_three hOut hbr
        · exact kdSporRow_Ly_five hOut hbr
      case Th =>
        rcases h with rfl | rfl
        · exact kdSporRow_Th_three hOut hbr
        · exact kdSporRow_Th_five hOut hbr
      case B => exact absurd rfl hB
      case M => exact absurd rfl hM
    · subst h; exact kdSporRow_M12_three hOut
    · subst h; exact kdSporRow_M22_three hOut
  · exact kdSporRow_of_not hs

end Certs

end CFSG.LocalAnalysis.GLTheoremA.KDSpor
