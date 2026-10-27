module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxMain

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

noncomputable def fusionZStarQuotEquivOfCoreQuot {X : Type} [Group X] {L : Subgroup X} {n : ℕ}
    (hn : 4 ≤ n) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n)) :
    ↥L ⧸ Open.fusionZStar ↥L ≃* alternatingGroup (Fin n) :=
  (Sol78.coreQuotientCenterEquiv ↥L).symm.trans ((Sol78.centerQuotCongr e).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simpa using hn))).trans QuotientGroup.quotientBot))

theorem maximalityLemmaInput_of_inputs (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) : Sol78.MaximalityLemmaInput := by
  intro X _ _ _ hna hK hz hU n hn hn9 _ hmaxdeg L hL ⟨eL⟩
  have hS : MaxSetting X n := ⟨hna, hK, hz, hU, hn, hn9, hmaxdeg⟩
  refine ⟨hL, fun K K₁ hLK hlt => ?_⟩
  have hKmem := Sol76.isSolomonMember_of_reflTransGen hL hLK.2
  obtain ⟨eLK⟩ := Sol76.nonempty_fusionZStar_equiv_of_reflTransGen hLK.2
  have eK := eLK.symm.trans (fusionZStarQuotEquivOfCoreQuot (by omega) eL)
  obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_solomonLt hPump hN1 hS hKmem eK hlt
  exact ⟨hL, hLK.2.tail ⟨⟨e.symm⟩, Or.inl hlt⟩⟩

end CFSG.ComponentClassification.SolMax
