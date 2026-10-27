module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Statement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwo

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI

theorem highRankEscapingStepCaseTwo_of_theoremC (hC : TheoremCStatement) :
    HighRankEscapingStepCaseTwo := by
  intro G _ _ S H z hset hz hzC u hu huS hsyl hrank hesc hII
  exfalso
  have hq : EscapingQuotientData H u := escapingQuotientData hset (hset.sylow_le huS) hu hesc
  obtain ⟨T, hT⟩ := exists_sylow_eq_escapingSylowImage hsyl
  have hzM : z ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hz.2.2 u huS).symm
  obtain ⟨hw2, hwT, hwC, hwne⟩ :=
    escapingMk_central_facts hset hz hzC hu huS hesc
      (w := ⟨z, hzM⟩) rfl
  have hTH : (T : Subgroup (EscapingQuotient u)) ≤ escapingImage H u :=
    hT ▸ escapingSylowImage_le_image hset.sylow_le
  have hcore : properTwoGenCoreGamma (T : Subgroup (EscapingQuotient u)) 2 ≤
      escapingImage H u :=
    iSup_le fun Q => iSup_le fun hQT => iSup_le fun hQ => hq.normalizer_le Q (hQT.trans hTH) hQ
  have hc : CoreConfig (escapingImage H u) (escapingBar u) (escapingMk u ⟨z, hzM⟩) := by
    refine coreConfig_escaping hq hTH hcore (hT ▸ hwT) (fun p hp => ?_) hw2 hwne
    have hp' : p ∈ escapingSylowImage S u := hT ▸ hp
    exact Subgroup.mem_centralizer_iff.mp hwC p hp'
  obtain ⟨J, hJ, huJ⟩ := hC _ _ _ _ hc
  exact huJ (hII J hJ)

theorem highRankEscapingStep_of_theoremC (hC : TheoremCStatement) : HighRankEscapingStep :=
  highRankEscapingStep_of_caseTwo (highRankEscapingStepCaseTwo_of_theoremC hC)

end CFSG.ProperTwoGeneratedCore.TheoremC
