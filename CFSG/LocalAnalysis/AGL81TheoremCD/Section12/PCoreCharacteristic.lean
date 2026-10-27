module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

variable {G : Type} [Group G]

theorem pCore_characteristic (p : ℕ) : (CFSG.pCore p G).Characteristic := by
  rw [CFSG.pCore_eq_iSup]
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun N => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hN => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hp => ?_
  exact le_iSup_of_le (N.map φ) (le_iSup_of_le (hN.map φ.toMonoidHom φ.surjective)
    (le_iSup_of_le (hp.map φ.toMonoidHom) le_rfl))

theorem normalizer_maxTwoLocal {M : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) :
    Subgroup.normalizer (M : Set G) = M := by
  refine le_antisymm ?_ (Subgroup.le_normalizer (H := M))
  have hchar : (CFSG.pCore 2 M).Characteristic := pCore_characteristic 2
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
    M (CFSG.pCore 2 M) hchar
  exact hle.trans_eq (CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_eq_normalizer_pCoreOf M hM).symm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
