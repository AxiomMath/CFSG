module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Row
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7OddCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem burgoyneE2TwistedE7OddCoreInput_holds : BurgoyneE2TwistedE7OddCoreInput := by
  intro K _ _ hK2 g a hα hns hcore
  have : Fintype K := Fintype.ofFinite K
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  rcases TwE7.twisted_core_or_mask_three hK2 n.pos hK L hα hns with h |
      ⟨h5, r, hr, h3, g₁, hg₁G, hconj, hcoc⟩
  · exact absurd h hcore
  · exact TwE7.burgTorusFor_twisted_three hK2 n.pos hK h5 L hα
      (TwE7.exists_twisted_reduction hK2 n.pos hK L hα hns).1 hr h3 hg₁G hconj hcoc

theorem burgoyneE2TwistedE7Input_holds : BurgoyneE2TwistedE7Input :=
  burgoyneE2TwistedE7Input_of_oddCore burgoyneE2TwistedE7OddCoreInput_holds

end CFSG.ComponentClassification.Burgoyne.E2
