module


public import CFSG.Open.RankThreeDefs
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerPerfectCoreContainment

variable {G : Type} [Group G]

theorem layer_le_perfectCore [Finite G] (H : Subgroup G) :
    CFSG.Open.rankThreeLayer H ≤ CFSG.Quasithin.perfectCore H := by
  refine sSup_le fun L hL => ?_
  obtain ⟨hLH, -, hq⟩ := hL
  have h := congrArg (Subgroup.map L.subtype) hq.1
  have hperf : ⁅L, L⁆ = L := by
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  exact CFSG.Quasithin.le_perfectCore_of_perfect hLH hperf

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerPerfectCoreContainment
