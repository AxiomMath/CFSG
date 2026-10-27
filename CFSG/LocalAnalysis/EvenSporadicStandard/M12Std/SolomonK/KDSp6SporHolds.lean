module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6Spor
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineLFourRankCases
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem sporadicNoE64_holds :
    SporadicNoE64 := by
  intro s hs E hE hcard
  rcases hs with rfl | rfl
  · have e : Carrier .HS ≃* NativeSporadic.HS := MulEquiv.refl _
    have h := CFSG.SeitzReduction.SporadicRefine.hs_card_lt_of_mul_self e hE
    rw [hcard] at h
    norm_num at h
  · have e : Carrier .ONan ≃* CFSG.ONSchreier.Pv := CFSG.ONSchreier.onEquivPv
    have hab : CFSG.Assembly.IsElemAbelian 2 E := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [sq]; exact hE x hx⟩
      have ha := hE a a.2
      have hb := hE b b.2
      have hab := hE (a * b) (E.mul_mem a.2 b.2)
      calc (a : Carrier .ONan) * b = a * (a * b * (a * b)) * b := by rw [hab, mul_one]
        _ = (a * a) * (b * a) * (b * b) := by group
        _ = b * a := by rw [ha, hb, one_mul, mul_one]
    have h := ONTwoRank.card_le_eight_of_mulEquiv_Pv e E hab
    rw [hcard] at h
    norm_num at h

end CFSG.EvenSporadicStandard.M12Std.SolomonK
