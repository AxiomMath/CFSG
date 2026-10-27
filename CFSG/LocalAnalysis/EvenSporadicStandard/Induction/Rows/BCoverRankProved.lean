module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MBShared
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CentralLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadic
public import CFSG.Sporadic.GLQ.BTwoRank
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census

section Rank

theorem bCoverRank_of_sporadicMultipliers (hSM : SporadicMultipliers) : BCoverRank := by
  intro X _ _ hq hX
  have hZ : Nat.card (center X) ∣ 2 :=
    card_center_dvd_of_sporadicMultipliers (s := .B) hSM
      CFSG.Sporadic.Bridge.B.nonempty_mulEquiv hq hX
  obtain ⟨f⟩ := hX
  obtain ⟨⟨V, hV, hVc⟩, -⟩ := CFSG.Sporadic.GLQ.b_two_rank_at_least_five (X ⧸ center X) ⟨f⟩
  have hr : ∀ A : Subgroup X, A ≤ (QuotientGroup.mk' (center X)).ker →
      (∀ a ∈ A, a * a = 1) → Nat.card A ≤ 2 ^ 1 := by
    intro A hA hsq
    rw [QuotientGroup.ker_mk'] at hA
    exact card_le_two_pow_of_dvd hsq ((Subgroup.card_dvd_of_le hA).trans hZ) (by norm_num)
  have := hV
  obtain ⟨A, hA, k, hk3, hAk⟩ := exists_elementaryAbelian_of_quotient (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hr V
    (by rw [hVc]; norm_num) (r := 1) (n := 5) (t := 3) (by intro k hk; omega)
  exact hk3.trans (CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) A hA hAk)

end Rank

end CFSG.EvenSporadicStandard.Induction.Hyp
