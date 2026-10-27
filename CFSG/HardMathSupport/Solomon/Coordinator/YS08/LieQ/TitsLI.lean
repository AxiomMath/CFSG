module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.ReeFamily
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.TitsV1
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.TitsSL2
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.TitsAct

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.ChevTwo.Semi CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

section TitsLISec


theorem titsLI : TitsLI := by
  intro K _ _ _ hK2 j
  have hK : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK2
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hj
  interval_cases j
  · refine reeLIOddAt_zero_of_witness hK ?_
    intro r hr hodd hne
    obtain ⟨g, hg⟩ : ∃ g : SL2 K, largeReeA1Hom K 0 g = r := by
      obtain ⟨g, hg⟩ := (rankOneEquivSL K 0 hK).surjective ⟨r, hr⟩
      exact ⟨g, congrArg Subtype.val hg⟩
    have hg1 : g ≠ 1 := fun h => hne (by rw [← hg, h, map_one])
    have hgo : Nat.Coprime (orderOf g) 2 := by
      rw [← orderOf_injective (largeReeA1Hom K 0) largeReeA1Hom_injective g, hg]
      exact hodd
    obtain ⟨w, hw, hmove⟩ := largeReeA1Hom_g3_moves_complement_zero hK
    refine ⟨w, hw, ?_⟩
    rcases sl2_odd_order_card_two hK2 g hgo hg1 with h | h
    · rw [← hg, h]
      exact hmove
    · rw [← hg, h, map_inv]
      intro hc
      exact hmove (Commute.inv_left_iff.1 hc)
  · exact reeLIOddAt_one hK

theorem lieQConstrained_two_holds : LieQConstrained 2 :=
  lieQConstrained_two_of_titsLI titsLI

end TitsLISec

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
