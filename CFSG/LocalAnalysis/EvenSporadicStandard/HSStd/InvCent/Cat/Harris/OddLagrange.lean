module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Props

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open CFSG CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_fixed_dvd_card_group {S : Type} [Group S] [Finite S] (σ : MulAut S) :
    Nat.card ↥(fixedSubgroup σ) ∣ Nat.card S :=
  Subgroup.card_subgroup_dvd_card _

theorem card_PSL_two_four (hO : LieOrderFormulasInput) {S : Type} [Group S]
    (hm : LieModel S .PSL 2 3 4) : Nat.card S = 265680 := by
  have hadm : StatedLieAdmissible .PSL 2 3 4 :=
    ⟨Nat.prime_three, by norm_num, by norm_num, by decide, by decide⟩
  have hord := (hO S .PSL 2 3 4 hadm hm).2.1
  have hn : lieOrderNumerator .PSL 2 (3 ^ 4) = 531360 := by decide
  have hd : lieOrderDivisor .PSL 2 (3 ^ 4) = 2 := by decide
  rw [hn, hd] at hord
  omega

theorem harrisOddSharp_PSL_two_four (hO : LieOrderFormulasInput) : HarrisOddSharp .PSL 2 4 := by
  intro S _ _ hm σ _ _ _
  have hdvd := card_fixed_dvd_card_group σ
  rw [card_PSL_two_four hO hm] at hdvd
  refine ⟨fun h => ?_, fun _ h => ?_⟩
  · rw [h] at hdvd
    exact absurd hdvd (by decide)
  · rw [h] at hdvd
    exact absurd hdvd (by decide)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
