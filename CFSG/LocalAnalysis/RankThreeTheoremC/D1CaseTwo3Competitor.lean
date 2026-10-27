module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Config
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Constrained
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitor

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.le_d1LayerX_of_le (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoData3 p P M H R Rbar) {H' : Subgroup G}
    {Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p)}
    (hd' : D1CaseTwoData3 p P M H' R Rbar') (hJH' : nclIn H (d1LayerX p H R) ≤ H') :
    d1LayerX p H R ≤ d1LayerX p H' R :=
  D1CaseTwoDataAt.le_d1LayerX_of_le (hSch := hSch) (hd := hd.toAt) (hd' := hd'.toAt) (hJH' := hJH')

theorem D1CaseTwoData3.false_of_constrained_competitor_of (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hgrp : CaseTwoGroupFacts) (hd : D1CaseTwoData3 p P M H R Rbar)
    {Y : Subgroup G} {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hLJ : L ≤ ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    {H' : Subgroup G} (hext' : D1Extremal p P M H' R) (hJH' : nclIn H Y ≤ H')
    (hcon : HasPrimeConstraint (G := H') p) : False := by
  have hiso := hd.cfg.red.isCaseTwoGroup_of_not_le3 hd.cfg.catalog hOut hS hd.cyclic hd.rank hL
    hLX₀
  obtain ⟨Jt, φ, hφs, -⟩ := exists_competitor_surj_of hd.cfg.red.prime hLX₀ hLJ
    hext'.primeCore_le hJH'
  exact d1CaseTwo_false_of_constrained hext' hcon hgrp hiso
    ((Subgroup.card_dvd_of_surjective (f := φ) hφs).trans (Subgroup.card_subgroup_dvd_card Jt))

theorem D1CaseTwoData3.false_of_constrained_competitor (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hgrp : CaseTwoGroupFacts) (hd : D1CaseTwoData3 p P M H R Rbar)
    {H' : Subgroup G} (hext' : D1Extremal p P M H' R)
    (hJH' : nclIn H (d1LayerX p H R) ≤ H') (hcon : HasPrimeConstraint (G := H') p) : False := by
  obtain ⟨L, hL, hLX₀⟩ := hd.exists_not_le hOut
  exact hd.false_of_constrained_competitor_of hOut hS hgrp hL hLX₀
    ((le_layer_of_isComponentOf hL).trans (hd.map_nclIn_eq le_rfl hd.map_d1LayerX_inf_ne_bot).ge)
    hext' hJH' hcon

theorem D1CaseTwoData3.competitor (hOut : KFactOutCyclic) (hC : D1CaseTwoComp3 G)
    (hS : KFactSeitzCyc) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoData3 p P M H R Rbar) {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H')
    (hJH' : nclIn H (d1LayerX p H R) ≤ H') (hRH' : R ≤ H') :
    ∃ Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p),
      D1CaseTwoData3 p P M H' R Rbar' ∧ d1LayerX p H R ≤ d1LayerX p H' R := by
  have hcfg := hd.cfg
  have hext' : D1Extremal p P M H' R := hcfg.ext.of_le hH' hRH' (hd.not_le_of_nclIn_le hOut hJH')
  by_cases hcon : HasPrimeConstraint (G := H') p
  · exact (hd.false_of_constrained_competitor hOut hS hC.grp hext' hJH' hcon).elim
  obtain ⟨Rbar', hcfg'⟩ := exists_componentConfig3 hcfg.glob hcfg.loc.sigma
    hcfg.loc.isCoreMaxLocal hext' hcon hcfg.ind
  obtain ⟨L, hL, hLX₀⟩ := hd.exists_not_le hOut
  have hall := hd.toAt.forall_isCyclic_of_competitor (kFactCycAut_of_kFactOutCyclic hOut) hS
    hInv.toIn hSch hL hLX₀
    ((le_layer_of_isComponentOf hL).trans (hd.map_nclIn_eq le_rfl hd.map_d1LayerX_inf_ne_bot).ge)
    hcfg'.toU hJH' (fun _ => hC.false_of_caseThree hcfg' (hd.exists_normalCyclic hOut hS hC.grp))
  have hd' : D1CaseTwoData3 p P M H' R Rbar' := D1CaseTwoData3.of_central hC.central hcfg' hall
  exact ⟨Rbar', hd', hd.le_d1LayerX_of_le hSch hd' hJH'⟩

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC
