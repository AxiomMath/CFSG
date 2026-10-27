module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinBlock

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ComponentClassification
  CFSG.LieType.Universal.Spin

theorem a2lCoverMinus43_holds
    (hC : HypA2.ChevOddInChev2) :
    a2lCoverOn fun S _ => LieModel S .POmegaMinus 4 3 1 := by
  intro K _ _ hq h2 hZ hm
  haveI : Group.IsPerfect K := hq.1
  obtain ⟨-, F, _, _, hcard, b, c, hirr, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  have hF3 : Fintype.card F = 3 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  have hk : ringChar F ≠ 2 := a2l_ringChar_ne_two (by rw [hF3]; decide)
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hk
  haveI := a2l_finite_spinMinus hirr 4
  have hN : Nat.card (center (spinGroup (quadMinus 4 F b c))) < 2 * 2 := by
    have := a2l_card_center_spinMinus_four_le_two hirr h2F
    omega
  obtain ⟨ψ⟩ := a2l_nonempty_equiv_of_cover (a2l_splits_spinMinus hk hirr (by norm_num)) h2 _
    (e.trans (spinQuotientCenterEquivQuadMinus (by norm_num) hirr).symm) hN
    (a2l_two_le_card_center h2 hZ)
  obtain ⟨E, _, _, Θ, hEc, hΘinj, hΘneg⟩ :=
    a2l_exists_spinMinus_sl2 hirr h2F 4 (⟨0, by decide⟩ : Fin (4 - 1))
  have hE9 : Fintype.card E = 9 := by
    rw [hEc, hcard]
    norm_num
  have hTU : HypA2.TypU K := a2l_typU_of_not_inChev2 hq h2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))))))
    (a2l_not_inChev2_pOmegaMinus43 hC hm)
  exact a2l_centralDatum_of_equiv ψ (by decide) (by norm_num) hE9 Θ hΘinj
    (a2l_mem_center_of_coe_eq_neg_one hΘneg) hTU

end CFSG.OddStandard.SmallF3.HypA2Leaves
