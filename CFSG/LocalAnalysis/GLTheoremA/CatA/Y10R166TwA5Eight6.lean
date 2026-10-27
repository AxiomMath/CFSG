module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Eight

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial


theorem evenRank_unitaryPSU_six {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 3 F) :
    evenRank (unitaryPSU h 6) = 4 := by
  have hK : Rk2IsLabel (unitaryPSU h 6) (⟨.twA, 5, 3⟩ : GLALabel) :=
    hasLabel_unitaryPSU_six h (by norm_num)
  have hlow : 4 ≤ evenRank (unitaryPSU h 6) :=
    (rk2Lower_holds (unitaryPSU h 6) (⟨.twA, 5, 3⟩ : GLALabel) hK).twa_one rfl (by norm_num)
  have hup : evenRank (unitaryPSU h 6) ≤ 4 :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds (K := unitaryPSU h 6)
      (lab := (⟨.twA, 5, 3⟩ : GLALabel)) hK).twa5 ⟨rfl, rfl⟩ (by norm_num)
      (center_unitaryPSU_six h (by norm_num))
  exact le_antisymm hup hlow

theorem twA5_mult_five {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 3 F) :
    (Subgroup.center ↥(blockSU h suFiveIndex) = ⊥ ∧
        TrivialMultiplierT ↥(blockSU h suFiveIndex)) ∧
      Odd (Nat.card (Subgroup.center ↥(blockSU h suFiveIndex))) ∧
      12 ≤ twoRank ↥(blockSU h suFiveIndex) ∧
      ∀ r : ℕ, Nat.Prime r → r ≠ 2 → r ∣ 2 ^ 6 - 1 →
        r ∣ Nat.card (↥(blockSU h suFiveIndex) ⧸ Subgroup.center ↥(blockSU h suFiveIndex)) := by
  have hfive := unitaryFive_mult (J := ↥(blockSU h suFiveIndex)) (n := 3) (by norm_num)
    (hasLabel_blockSU_five h) CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  obtain ⟨hsix, hodd, hm2, hdvd⟩ := hfive
  have hnot : ¬ Even 3 := by norm_num
  rcases hsix with h | h
  · exact ⟨h, hodd, by simpa using hm2, by simpa using hdvd⟩
  · exact absurd h hnot

end TwA5Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F
