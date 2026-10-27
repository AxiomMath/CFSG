module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSimpleFitting
public import CFSG.Sporadic.SmallOddCore.HSMcL
public import CFSG.Sporadic.ONOddCore.Head

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem l34Prop41End_of_inputs
    (hSyl : L34EndSylowStep) (hGH : GorensteinHarrisInput) (hON : ONanSylowInput) :
    L34Prop41End := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv
  obtain ⟨⟨hsimple, hnab, hK, ⟨z, hz2, hzO⟩, -⟩, -⟩ := id hset
  have : IsSimpleGroup G := hsimple
  obtain ⟨P, -, hcase⟩ := hSyl G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv
  obtain ⟨-, -, -, -, htop⟩ := SmallLocal.simple_generalized_fitting_self G hnab
  let eF : CFSG.generalizedFitting G ≃* G := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hFs : IsSimpleGroup (CFSG.generalizedFitting G) := eF.isSimpleGroup
  rcases hcase with ⟨T, hT⟩ | ⟨T, hT⟩
  · obtain ⟨φ⟩ := hGH G hnab hK P T hT
    exact hzO (Sporadic.SmallOddCore.ctu_catalog_hs_mcl_almost_simple_odd_core_vanishing hFs
      (Or.inl ⟨eF.trans φ⟩) z hz2)
  · obtain ⟨φ⟩ := hON G hnab hK P T hT
    have h := Sporadic.ONOddCore.ctuc_on_generalized_fitting_involution_centralizer_odd_core_trivial
      hFs ⟨eF.trans φ⟩
    exact hzO (h.2 z hz2)

end CFSG.ComponentClassification.GrSLit
