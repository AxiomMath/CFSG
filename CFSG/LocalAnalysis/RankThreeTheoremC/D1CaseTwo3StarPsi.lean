module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarPsi
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NoSPCz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Constrained

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Star

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.extremal_of_normalizer_le (hd : D1CaseTwoData3 p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) {Hs : Subgroup G} (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs) :
    Subgroup.centralizer ({(z : G)} : Set G) ≤ Hs ∧
      Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) ≤ Hs ∧
      D1Extremal p P M Hs R :=
  D1CaseTwoDataAt.extremal_of_normalizer_le (hd := hd.toAt) (hz := hz) (hHs := hHs) (hLHs := hLHs)

theorem D1CaseTwoData3.exists_componentConfig_star (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hgrp : CaseTwoGroupFacts) (hd : D1CaseTwoData3 p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) {Hs : Subgroup G} (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs) :
    ∃ Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p),
      D1ComponentConfig3 p P M Hs R Rbars := by
  obtain ⟨hCHs, -, hext⟩ := D1CaseTwoData3.extremal_of_normalizer_le hd hz hHs hLHs
  have hcon : ¬ HasPrimeConstraint (G := Hs) p := by
    intro hcon
    obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := id hz
    have hiso : IsCaseTwoGroup p L :=
      hd.cfg.red.isCaseTwoGroup_of_not_le3 hd.cfg.catalog hOut hS hd.cyclic hd.rank hL hLX
    obtain ⟨A₀, f, hf⟩ := D1CaseTwoData3.exists_surjective_czQuot hd hL hzp hzL
    refine d1CaseTwo_false_of_constrained hext hcon hgrp hiso ?_
    exact (Subgroup.card_dvd_of_surjective (f := f) hf).trans
      ((Subgroup.card_subgroup_dvd_card A₀).trans
        ((Subgroup.card_dvd_of_surjective (f := d1StarPsi p hCHs)
          (d1StarPsi_surjective p hCHs)).trans (Subgroup.card_subgroup_dvd_card _)))
  exact exists_componentConfig3 hd.cfg.glob hd.cfg.loc.sigma hd.cfg.loc.isCoreMaxLocal hext hcon
    hd.cfg.ind

end Star

end CFSG.LocalAnalysis.RankThreeTheoremC
