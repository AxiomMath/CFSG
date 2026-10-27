module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Cores
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxOfHyp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY3b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY9
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY10
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY13

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3.HarrisU33
open CFSG.ComponentClassification.StandardRecognition

theorem smallF3U33Core_of_fritz
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput)
    (hCI : ClassicalInvolutionTheoremModels) (hB : Harris1981Bound) (hF : FritzFusionInput)
    (hCtx : FritzCtxInput) (hI : FzCaseI) (hR2 : FzCaseIIr2)
    (hY7 : FzY7) (hY8 : FzY8) (hY10 : FzY10Shape) (hGlue : FzSylowOfClosure) :
    SmallF3U33Core := by
  intro G _ _ L hC hnc hQ
  haveI : IsSimpleGroup G := hC.simple
  obtain ⟨t, hhyp⟩ := exists_hyp_of_smallF3Cyclic hC hQ
  obtain ⟨S, x₁, x₂, lam, rho, h0⟩ := exists_ctx0_of_hyp hhyp
  have hr4 := not_four_generated_of_ctx0 hGH hC.nonab hnc h0
  by_cases hI' : invCent t = twoCore t ⊔ L
  · exact hI G t L S x₁ x₂ lam rho hr4 h0 hI'
  · obtain ⟨tau, h⟩ := hCtx G t L S x₁ x₂ lam rho h0 hI'
    have hbound : ¬ 2 ^ 11 ∣ Nat.card G := fun hd => hB G L t hhyp hC.kProper hnc hd
    rcases fzCardTwoCoreCtx_holds G t L S x₁ x₂ lam rho tau h with hr | hr
    · obtain ⟨T₂, hT⟩ := exists_isFzT2 h.isPGroup (fz_S_le_N2 h)
      by_cases hs : FzSylow T₂
      · obtain ⟨a₁₂, a₂₂, a₃₂, hsh⟩ := hY10 G t L S T₂ x₁ x₂ lam rho tau hr4 h hr hT hs
        exact hnc (fz_catalog_of_shape hCI hGlue hC.nonab h0 hs hsh
          (hF G t L S x₁ x₂ lam rho tau T₂ a₁₂ a₂₂ a₃₂ h hr hT hs hsh))
      · by_cases hab : IsMulCommutative (fzP t x₁ x₂ rho)
        · exact hbound (hY7 G t L S T₂ x₁ x₂ lam rho tau hr4 h hr hT hs hab)
        · exact hY8 G t L S T₂ x₁ x₂ lam rho tau hr4 h hr hT hs hab hbound
    · exact hR2 G t L S x₁ x₂ lam rho tau hbound hr4 h hr

end CFSG.OddStandard.SmallF3.FritzII
