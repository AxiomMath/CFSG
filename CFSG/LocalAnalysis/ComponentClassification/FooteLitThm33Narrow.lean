module

public import CFSG.LocalAnalysis.ComponentClassification.CTUFooteConjugate
public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClass

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

theorem footeConjugatePairExclusion_of_maximalStep
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hstep : FooteSolomonMaximalStep) : FooteConjugatePairExclusion := by
  have hM3 : FooteSolomonFamilyInput := footeSolomonFamilyInput_of_maximalStep
    (Sol76.aschbacherRankOneInput_of_classicalInvolution hCI hGA) hstep
  intro G _ _ t L hmin hce hsimp hrank2 c s X hc hs hcs hXF hXc hXs
  obtain ⟨u, -, v, -, huv⟩ := exists_mul_ne_mul_of_footeCounterexample hce
  have hSol : ∀ N : Subgroup G, IsKBalanced N →
      solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G) :=
    fun N hN => absurd hN (h13 G hsimp ⟨u, v, huv⟩ hce.1.1 N)
  have hsC : s ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.mpr hcs.symm
  have hXsc : IsTwoComponentIn (conjugate X s) (centralizer ({c} : Set G)) :=
    ⟨UnbalancedCorr.conjugate_le_of_mem hXc.1 hsC,
      UnbalancedCorr.isPComponent_conjugate_subgroupOf hsC hXc.2⟩
  exact hXs (foote_theorem_3_3_of_local hSol hM3
    (fun B hB hfam => card_center_le_two_of_footeFamilyType hGA hGC hSA G B hB hfam)
    hmin hce hrank2 ⟨hc, hXsc.1, hXsc.2⟩ ⟨hc, hXc.1, hXc.2⟩ (conjugate_mem_footeFamilyOf hXF s)
    hXF)

end CFSG.ComponentClassification.FooteLit
