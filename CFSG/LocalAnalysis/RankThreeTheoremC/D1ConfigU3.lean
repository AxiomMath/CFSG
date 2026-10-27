module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3
public import CFSG.LocalAnalysis.AGLEmbedding.D1ConfigU

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1GlobalU D1LocalU D1ComponentConfigU D1At D1ConstrainedCaseAt
  D1CaseOneSmallAt D1CaseTwoAt D1CaseThreeAt D1CaseOneLieAt)

variable {G : Type} [Group G] [Finite G]

theorem Setting.toU (hS : Setting G) : D1GlobalU G where
  simple := hS.simple
  nonab := hS.nonab
  kProper := hS.kProper
  charTwo := hS.charTwo
  rank := hS.rank.ge
  pre := fun q hq => absurd (CFSG.AGLEmbedding.four_le_evenRank_of_mem_betaFour hq)
    (by rw [hS.rank]; omega)
  preSigma := hS.pre

theorem D1Local3.toU {p : ℕ} {P : Sylow p G} {M : Subgroup G} (h : D1Local3 p P M) :
    D1LocalU p P M :=
  ⟨h.sigma, h.maxLocal, h.core⟩

theorem d1At3_iff_d1At (q : ℕ) : D1At3 G q ↔ D1At G q :=
  ⟨fun h Q M hM hW H hH hr => h Q M ⟨hM, hW⟩ H hH hr,
    fun h Q M hM H hH hr => h Q M hM.1 hM.2 H hH hr⟩

section Config

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfig3.toU (h : D1ComponentConfig3 p P M H R Rbar) :
    D1ComponentConfigU p P M H R Rbar where
  glob := h.glob.toU
  loc := h.loc.toU
  ext := h.ext
  notCon := h.notCon
  ind := fun q hq hqp => (d1At3_iff_d1At q).mp (h.ind q hq hqp)
  rbar := h.rbar
  red := h.red
  catalog := h.catalog

end Config

end CFSG.LocalAnalysis.RankThreeTheoremC
