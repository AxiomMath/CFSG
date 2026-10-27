module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Competitor
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitor

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.competitor_of (hOut : KFactOutCyclic) (hC : D1CaseTwoComp3 G)
    (hS : KFactSeitzCyc) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoData3 p P M H R Rbar) {Y : Subgroup G}
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hLJ : L ≤ ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H Y ≤ H') (hRH' : R ≤ H') :
    ∃ Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p), D1CaseTwoData3 p P M H' R Rbar' := by
  have hcfg := hd.cfg
  have hH'M : ¬ H' ≤ M := fun hH'M => hLX₀ (hLJ.trans
    (Subgroup.map_mono fun j hj => ⟨j.2, hH'M (hJH' hj)⟩))
  have hext' : D1Extremal p P M H' R := hcfg.ext.of_le hH' hRH' hH'M
  by_cases hcon : HasPrimeConstraint (G := H') p
  · exact (hd.false_of_constrained_competitor_of hOut hS hC.grp hL hLX₀ hLJ hext' hJH' hcon).elim
  obtain ⟨Rbar', hcfg'⟩ := exists_componentConfig3 hcfg.glob hcfg.loc.sigma
    hcfg.loc.isCoreMaxLocal hext' hcon hcfg.ind
  exact ⟨Rbar', D1CaseTwoData3.of_central hC.central hcfg'
    (hd.toAt.forall_isCyclic_of_competitor (kFactCycAut_of_kFactOutCyclic hOut) hS hInv.toIn hSch
      hL hLX₀ hLJ hcfg'.toU hJH'
      (fun _ => hC.false_of_caseThree hcfg' (hd.exists_normalCyclic hOut hS hC.grp)))⟩

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC
