module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisRank
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisTransport

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem cfAutPSL2Sylow : HarrisLit.AutPSL2SylowInput := by
  intro Y _ _ p f hp hp2 hfe h16 hY K hIK hk T hTK hP
  obtain ⟨F, _, _, Φ, hH, hI, hFA, hFAany⟩ := harris_context hp hp2 hfe h16 hY
  have hK' : pGammaL2PSLRange F ≤ K.map Φ.toMonoidHom := hI ▸ Subgroup.map_mono hIK
  have hk' : ∃ k ∈ K.map Φ.toMonoidHom, IsFieldInvModel k := by
    obtain ⟨k, hkK, hk⟩ := hk
    exact ⟨Φ k, Subgroup.mem_map_of_mem _ hkK, (hFA k).mp hk⟩
  have hT' : IsSylowIn (T.map Φ.toMonoidHom) (K.map Φ.toMonoidHom) :=
    ((isSylowIn_iff T K).mpr ⟨hTK, hP⟩).map Φ
  obtain ⟨g, -, -, hshape⟩ := hH.exists_sylowShape hK' hk' hT'
  refine ⟨⟨Φ.symm (MulAut.conj g (vStd F (K.map Φ.toMonoidHom))), ?_⟩, fun Q hQ => ?_⟩
  · have := hshape.pullback Φ hI hFA hFAany
    rwa [map_symm_map_mulEquiv] at this
  · apply exists_closure_map Φ.symm
    exact hH.rank_le_three hK' hk' hT' (Subgroup.map_mono hQ)

end CFSG.ComponentClassification.AutL2Facts
