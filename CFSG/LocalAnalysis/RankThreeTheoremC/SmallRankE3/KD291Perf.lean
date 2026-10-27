module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291GammaP
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291LinUni

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt KDInndiagP5)

section Assembly

theorem gammaStructureP_of_tables (hΔ : KDInndiagP5)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSp : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : GammaStructureP := by
  intro p hp hp5 X _ _ P x hcat hxP hx1 hx5 hP hC hperf hcomp
  haveI : Fact p.Prime := ⟨hp⟩
  have hxo : orderOf x = p := orderOf_eq_prime hx5 hx1
  obtain ⟨L, hLn, hq, hZp, hZ, hsimple, hnab, hLcat, hcen, hzcl⟩ :=
    kd291_comp_data hp hp5 hGA hSp P hcat hxP hx1 hx5 hP hC hcomp
  have hcatY : CFSG.AGLEmbedding.CatalogSimpleSections
      (X ⧸ primeComplementCore (G := X) p) := hcat.quotient _
  have hperfY := kd291_perf_quot hperf
  have hY3 : Open.pRank p (⊤ : Subgroup (X ⧸ primeComplementCore (G := X) p)) = 3 :=
    kd291_pRank_quot hp P hP
  have hxo' := kd291_orderOf_mk hp hxo
  have hC' := kd291_pRank_cent_quot hp hxo hC.le
  have hnlu := kd291_not_lu hp hp5 hGA L hq hZp hcen hperfY hY3.le hxo' hC'
  have hnlu' : ¬ IsLinearOrUnitaryAt p ↥L := kd291_not_lu_of_center_bot L hZ hnlu
  have hxL : (QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p) ∈ L :=
    kd291_mem_of_perf hp hp5 hΔ L hsimple hnab hLcat hnlu' hcen hperfY hxo'
  exact ⟨L, hLn, hsimple, hnab, hLcat, hnlu', hcen, hxL, hzcl⟩

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
