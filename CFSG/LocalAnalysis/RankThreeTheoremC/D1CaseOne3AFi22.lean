module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3SporSections
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ADefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Fi22

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmall3Data.false_of_isFi22 (hsec : SporSectionFacts3)
    (hd : D1OneSmall3Data p P M H R Rbar K) (hFi : IsFi22 K) : False := by
  obtain ⟨e⟩ := hFi
  obtain ⟨hsimple, hnonab⟩ := hd.toCore.isSimpleGroup
  have eq : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  haveI : IsSimpleGroup K := hsimple
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := eq.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnonab
  refine false_of_mem_sectionExcluded3 hsec hd.cfg.glob.rank (primeComplementCore (G := H) p)
    (K := K) inferInstance ⟨eq a, eq b, fun h => hab (eq.injective ?_)⟩ (s := .Fi22) (by simp)
    (eq.symm.trans e)
  rw [map_mul, map_mul]
  exact h

end Fi22

end CFSG.LocalAnalysis.RankThreeTheoremC
