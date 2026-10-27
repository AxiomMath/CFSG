module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisTransport
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem cfAutPSL2Centralizer : HarrisLit.AutPSL2CentralizerInput := by
  intro Y _ _ p f hp hp2 hfe h16 hY
  obtain ⟨F, _, _, Φ, hH, hI, hFA, hFAany⟩ := harris_context hp hp2 hfe h16 hY
  refine ⟨fun k hk ι hι h2 => ?_, ?_⟩
  · rw [hFA] at hk ⊢
    rw [map_mul]
    refine isFieldInvModel_mul hH.odd hk ?_ (by rw [← map_mul, ← map_pow, h2, map_one])
    rw [← hI]
    exact Subgroup.mem_map_of_mem _ hι
  · intro K hIK T hTK hP v hv k hkK hk Q hQK hQ hQC
    have hK' : pGammaL2PSLRange F ≤ K.map Φ.toMonoidHom := hI ▸ Subgroup.map_mono hIK
    have hT' : IsSylowIn (T.map Φ.toMonoidHom) (K.map Φ.toMonoidHom) :=
      ((isSylowIn_iff T K).mpr ⟨hTK, hP⟩).map Φ
    have hv' := SylowShape.pushforward Φ hI hFA hFAany hv
    have hkK' : Φ k ∈ K.map Φ.toMonoidHom := Subgroup.mem_map_of_mem Φ.toMonoidHom hkK
    have hQC' : Q.map Φ.toMonoidHom ≤ centralizer {Φ k} := by
      rw [← map_centralizer_singleton]
      exact Subgroup.map_mono hQC
    have h := hH.card_le_of_centralizer hK' hT' hv' hkK' ((hFA k).mp hk)
      (Q := Q.map Φ.toMonoidHom) (Subgroup.map_mono hQK) (hQ.map _) hQC'
    rwa [card_map_mulEquiv, ← hI, ← map_inf_mulEquiv, ← map_zpowers_mulEquiv,
      ← Subgroup.map_sup, card_map_mulEquiv] at h

end CFSG.ComponentClassification.AutL2Facts
