module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Basic

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit

theorem knownRowThree_of_isTwoQuasisimple (hKR : T1.KnownRowThree) {Y : Type} [Group Y]
    [Finite Y] (hY : IsTwoQuasisimple Y) (hcat : Blueprint.Catalog (Y ⧸ Open.fusionZStar Y))
    {z : Y} (hz : orderOf z = 2) {L : Subgroup Y} (hL : IsTwoComponentIn L (centralizer {z}))
    (hzL : z ∈ L) (hI : T1.InductionType 3 ↥L) :
    IsChevalleyOver 3 (Y ⧸ pPrimeCore 2 Y) ∨
      Nonempty (Y ⧸ pPrimeCore 2 Y ≃* ↥Blueprint.NativeSporadic.M11) := by
  have htop := T23.oPrimeResidual_two_eq_top hY.1
  let e : ↥(GH74.GLS.oPrimeResidual 2 Y) ≃* Y :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hN : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 Y) :=
    isTwoQuasisimple_of_mulEquiv e.symm hY
  have hcat' : Blueprint.Catalog (↥(GH74.GLS.oPrimeResidual 2 Y) ⧸
      Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 Y)) := by
    obtain ⟨eZ⟩ :=
      CFSG.ComponentClassification.FooteLit.nonempty_quotient_fusionZStar_equiv e
    exact SectionRank.catalog_of_mulEquiv eZ hcat
  rcases hKR Y hN hcat' z hz L (.inl hL) hzL hI with h | h
  · exact .inl (T23.isChevalleyOver_of_mulEquiv
      (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) h)
  · exact .inr h

end CFSG.OddStandard.HigherRank.F3
