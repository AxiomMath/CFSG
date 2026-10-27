module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinBlock

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ComponentClassification
  CFSG.LieType.Universal.Spin

theorem a2lCoverO73_holds
    (hC : HypA2.ChevOddInChev2) :
    a2lCoverOn fun S _ => LieModel S .POmegaOdd 3 3 1 := by
  intro K _ _ hq h2 hZ hm
  haveI : Group.IsPerfect K := hq.1
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  have hF3 : Fintype.card F = 3 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  have hk : ringChar F ≠ 2 := a2l_ringChar_ne_two (by rw [hF3]; decide)
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hk
  have hirr := a2l_irr_zero_one hF3 h2F
  haveI := a2l_finite_spinOdd h2F 3
  have hN : Nat.card (center (spinGroup (quadOdd 3 F))) < 2 * 2 := by
    have := a2l_card_center_spinOdd_le_two h2F (n := 3) (by norm_num)
    omega
  obtain ⟨ψ⟩ := a2l_nonempty_equiv_of_cover (a2l_splits_spinOdd hk (by norm_num)) h2 _
    (e.trans (spinQuotientCenterEquivQuadOdd h2F (by norm_num)).symm) hN
    (a2l_two_le_card_center h2 hZ)
  obtain ⟨E, _, _, Θ, hEc, hΘinj, hΘneg⟩ :=
    a2l_exists_spinMinus_sl2 hirr h2F 3 (⟨1, by decide⟩ : Fin (3 - 1))
  have hE9 : Fintype.card E = 9 := by
    rw [hEc, hcard]
    norm_num
  have hφinj : Function.Injective ((a2lMinusToOdd F).spinGroupMap.comp Θ) :=
    (a2l_spinGroupMap_minusToOdd_injective F h2F hirr).comp hΘinj
  have hz : ((a2lMinusToOdd F).spinGroupMap.comp Θ) (a2lNegOne E) ∈
      center (spinGroup (quadOdd 3 F)) :=
    a2l_mem_center_of_coe_eq_neg_one (a2l_coe_spinGroupMap_eq_neg_one _ hΘneg)
  have hTU : HypA2.TypU K := a2l_typU_of_not_inChev2 hq h2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))))
    (a2l_not_inChev2_pOmegaOdd33 hC hm)
  exact a2l_centralDatum_of_equiv ψ (by decide) (by norm_num) hE9 _ hφinj hz hTU

end CFSG.OddStandard.SmallF3.HypA2Leaves
