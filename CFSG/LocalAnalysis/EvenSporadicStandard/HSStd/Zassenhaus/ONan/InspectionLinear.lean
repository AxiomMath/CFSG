module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionArms
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionCommon
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.CenterFree
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21L52a
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint

private theorem orderOf_ne_ten_of_lieModel_psl_five_two {N : Type} [Group N]
    (hN : LieModel N .PSL 5 2 1) (g : N) : orderOf g ≠ 10 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hN
  have hK2 : Nat.card K = 2 := by simpa using hK
  let := CFSG.EvenSporadicStandard.M22Std.P21L52.charTwo hK2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  exact CFSG.EvenSporadicStandard.M22Std.P21L52.no_order_ten_of_equiv hK2 e g

theorem inspectionArm_psl_three_seven : InspectionArm fun N _ => LieModel N .PSL 3 7 1 := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_lieModel_psl_three_seven hQ
  have hidx : N.index ≤ 6 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_lieModel_psl_three_seven hQ)
  obtain ⟨_, _, _, A, _, _, _, _, _, hAN, hA, _, _, _⟩ :=
    exists_simple_le_of_pgl29 (N := N) (by omega) hw
  have hdvd : Nat.card A ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hAN
  have hSt : CFSG.Open.StatedClassicalModel ↥N .PSL 3 7 1 :=
    LieModel.statedClassicalModel hQ (by decide)
  have hNcard : Nat.card ↥N = 1876896 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_seven hSt
  rw [hA, hNcard] at hdvd
  exact absurd hdvd (by norm_num)

theorem inspectionArm_psl_five_two : InspectionArm fun N _ => LieModel N .PSL 5 2 1 := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_lieModel_psl_five_two hQ
  have hidx : N.index ≤ 2 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_lieModel_psl_five_two hQ)
  obtain ⟨w, hw2, H, _, hH, hwH, _, ⟨d, hdH, hd⟩, _, _, _, _, _, _⟩ :=
    exists_simple_le_of_pgl29 (N := N) (by omega) hw
  have hwd : w * d = d * w := (Subgroup.mem_centralizer_singleton_iff.1 (hH hdH)).symm
  have hdw : ∀ k : ℕ, d ^ k ≠ w := fun k h => hwH (h ▸ pow_mem hdH k)
  obtain ⟨x, hxN, hx⟩ := exists_mem_orderOf_eq_ten hidx hw2 hd hwd hdw
  have hxN10 : orderOf (⟨x, hxN⟩ : ↥N) = 10 := by rw [Subgroup.orderOf_mk, hx]
  exact orderOf_ne_ten_of_lieModel_psl_five_two hQ (⟨x, hxN⟩ : ↥N) hxN10

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
