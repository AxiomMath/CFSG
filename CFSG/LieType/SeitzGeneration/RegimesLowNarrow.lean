module

public import CFSG.LieType.SeitzGeneration.LowNarrow

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem seitzInnerLow_of_regimes (hCI : SeitzInnerLowClassical) (hPar : SeitzExcParabolic)
    (hAni : SeitzExcAnisotropic) : SeitzInnerLow :=
  SeitzPlanes.of_cover (fun d _ _ _ E hE => by
    by_cases h : IsClassicalIndex d.1
    exacts [Or.inl ⟨hE.1, hE.2, h⟩, Or.inr ⟨hE.1, hE.2, h⟩]) hCI (seitzExcLow_of hPar hAni)

theorem kFactSeitzRankTwoInnerEx_of_regimes (hCEx : InnerExFor fun d => IsClassicalIndex d.1)
    (hPar : SeitzExcParabolic) (hParEx : ExcParabolicPlane) (hAni : SeitzExcAnisotropic) :
    KFactSeitzRankTwoInnerEx := by
  have hXI := seitzExcLow_of hPar hAni
  refine kFactSeitzRankTwoInnerEx_of_for hCEx ?_
  intro d hx p hp hp2 hpd hex ⟨E, hE, hc, hi⟩
  by_cases hr : RankLE2 p (Cat d)
  · exact ⟨E, hE, hc, hi, hXI d p hp hp2 hpd hex E hE hc ⟨hi, hr, hx⟩⟩
  · obtain ⟨E₁, hE₁, hc₁, hi₁, hN₁⟩ := hParEx d p hp hp2 hpd hex hx hr
    exact ⟨E₁, hE₁, hc₁, hi₁, hPar d p hp hp2 hpd hex E₁ hE₁ hc₁ ⟨hi₁, hx, hN₁⟩⟩

theorem innerEx_lowN_of_regimes (hCEx : InnerExFor fun d => IsClassicalIndex d.1)
    (hCI : SeitzInnerLowClassical) (hCON : SeitzOuterLowNarrow)
    (hPar : SeitzExcParabolic) (hParEx : ExcParabolicPlane) (hAni : SeitzExcAnisotropic)
    (hXON : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      (¬ IsClassicalIndex d.1 ∨ (p = 3 ∧ IsDFourIndex d.1))) :
    KFactSeitzRankTwoInnerEx ∧ KFactSeitzRankTwoLowN :=
  ⟨kFactSeitzRankTwoInnerEx_of_regimes hCEx hPar hParEx hAni,
    seitzInnerLow_of_regimes hCI hPar hAni, SeitzOuterLowN.of_regimes hCON hXON⟩

end CFSG.LieType.SeitzGeneration
