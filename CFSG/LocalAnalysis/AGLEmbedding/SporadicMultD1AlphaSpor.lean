module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaMultipliers
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1
public import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi24
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowHN
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowJ3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowLy
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowSuz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowTh
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlpha
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall3

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem kFactAlphaSpor_of_multD1
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hD : SporadicMultipliersD1) : KFactAlphaSpor := by
  intro K _ _ hK s ⟨e⟩
  by_cases hBM : s = .B ∨ s = .M
  · refine kFactAlphaConclusion_of_hopfMultiplier hK e fun p hp hp2 hdvd => ?_
    by_cases hp3 : p = 3
    · subst hp3
      rcases hBM with rfl | rfl <;> exact hD.three _ (by decide) hdvd
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
        omega
      exact hD.big s p hp hp5 hdvd
  · obtain ⟨b⟩ := hbr s
    have hrow : SporadicAlphaData (NativeSporadic.Carrier s) := by
      cases s with
      | M11 => exact sporadicAlphaData_M11
      | M12 => exact sporadicAlphaData_M12
      | M22 => exact sporadicAlphaData_M22
      | M23 => exact sporadicAlphaData_M23
      | M24 => exact sporadicAlphaData_M24
      | J1 => exact sporadicAlphaData_J1
      | J2 => exact sporadicAlphaData_J2
      | J4 => exact sporadicAlphaData_J4
      | HS => exact sporadicAlphaData_HS
      | He => exact sporadicAlphaData_He
      | Ru => exact sporadicAlphaData_Ru
      | J3 => exact sporadicAlphaData_J3
      | McL => exact sporadicAlphaData_McL
      | Suz => exact sporadicAlphaData_Suz
      | ONan => exact sporadicAlphaData_ONan
      | Co2 => exact sporadicAlphaData_Co2
      | Co3 => exact sporadicAlphaData_Co3
      | Fi22 => exact sporadicAlphaData_Fi22
      | Fi23 => exact sporadicAlphaData_Fi23
      | Th => exact sporadicAlphaData_Th
      | Co1 => exact sporadicAlphaData_Co1
      | Fi24Prime => exact sporadicAlphaData_Fi24
      | HN => exact sporadicAlphaData_HN
      | Ly => exact sporadicAlphaData_Ly
      | B => exact (hBM (Or.inl rfl)).elim
      | M => exact (hBM (Or.inr rfl)).elim
    exact kFactAlphaConclusion_of_data coverModuleLemma coverAbelianSylowLemma coverRankLiftLemma
      K hK (e.trans b.symm) hrow

end CFSG.AGLEmbedding
