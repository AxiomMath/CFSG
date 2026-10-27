module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Beta
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Steps
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Statement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem zLayerWeakCoreFact3_of_facts (hList : KFactAlphaListM3)
    (hSmall : KFactAlphaSmallAut3Card) (hOn : KFactAlphaOnan3Comm) (hLift : KFactSL3LiftGen) :
    ZLayerWeakCoreFact3 := by
  intro X _ _ hcat he3 hcore P z hrank hz3 hzn hzc hzE hcyc hD
  obtain ⟨D, hD, hzD, hDn⟩ := hD
  have hDP : D ≤ (P : Subgroup X) := hD.elim (fun h => h.1) (fun h => h.1)
  have hD3 : ∀ x ∈ D, x ^ 3 = 1 := by
    rcases hD with hD | hD
    · have := hD.2.1
      exact fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) x hx
    · exact hD.2.2.1
  have h : ZLayerData3 X P z := ⟨hcat, he3, hcore, hrank, hz3, hzn, hDP hzD, hzc, hzE, hcyc⟩
  refine sSup_le fun K hK => ?_
  by_cases hZ : center K = ⊥
  · exact h.le_core_of_center_eq_bot hK hZ
  · by_contra hnot
    exact hnot (h.le_core_of_beta hK hZ (h.normalizes_of_not_le_core hK hZ hnot)
      (h.omega_of_not_le_core hK hZ hnot) hDP hD3 hzD hDn hList hSmall hOn hLift)

end CFSG.LocalAnalysis.RankThreeTheoremC
