module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem center_specialLinear_eq_bot_of_coprime {F : Type} [Field F] [Finite F] {N : ℕ}
    (hcop : Nat.Coprime N (Nat.card F - 1)) : center SL(N, F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [mem_bot]
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hc
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Subsingleton.elim _ _
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hc
    exact zero_ne_one hc
  have : Fintype F := Fintype.ofFinite F
  have hq : c ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one c hc0
  have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hc, hq⟩
  apply Subtype.ext
  rw [← hcA, hc1, map_one]
  rfl

end CFSG.SeitzReduction.SymplecticPilot
