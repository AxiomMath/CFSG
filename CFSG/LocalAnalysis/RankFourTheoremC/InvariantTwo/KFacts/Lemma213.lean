module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213CaseB
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Signalizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.ComponentClassification.OuterAutomorphisms Subgroup

namespace Red

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

theorem outer_solvable (R : Red n p K P z D) (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections K) (C : ComponentIndex K) :
    Group.IsSolvable (Outer C.1) := by
  obtain ⟨hsimple, hnonab⟩ := R.isSimpleGroup_comp C
  exact hS C.1 hsimple hnonab (hcat.simple_subgroup C.1 hsimple hnonab)

end Red

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG CFSG.LocalCores CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 Subgroup

theorem kFactLemma213Red_four_of_sigma (hI : GL83I294Two) (hB : GL83I203Sigma)
    (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) : KFactLemma213Red 4 := by
  intro p hp hp2 K _ _ hcat hcore hnc hpc P z D hconf hg hemb
  obtain ⟨g, hg⟩ := hg
  have h5 : 5 ≤ p := hconf.five_le hp hp2 le_rfl
  let R : Red 4 p K P z D := ⟨hp, hcore, hnc, hpc, hconf⟩
  by_cases hrk : ∃ d ∈ D, d ∉ zpowers z ∧ 3 ≤ CFSG.Open.pRank p (centralizer ({d} : Set K))
  · obtain ⟨d, hd, hdz, h3⟩ := hrk
    exact Or.inr fun y hy hy1 =>
      hconf.exists_mem_normalizer_zpowers_eq_of_three_le_pRank hp hd hdz h3 y hy hy1
  push Not at hrk
  by_cases hD : ∀ w ∈ D, ∀ C : ComponentIndex K, w • C = C
  · obtain ⟨d, hd, hdz⟩ := hconf.exists_mem_notMem_zpowers hp
    have hlow : ∃ x ∈ D, x ≠ 1 ∧ CFSG.Open.pRank p (centralizer ({x} : Set K)) ≤ 2 :=
      ⟨d, hd, fun h1 => hdz (h1 ▸ one_mem _), by have := hrk d hd hdz; omega⟩
    rcases R.caseA hI h5 (by norm_num) hcat hg hlow hD with h1 | h2
    · exact Or.inl h1
    · exact Or.inr fun y hy hy1 => h2 z R.conf.mem R.z_ne_one y hy hy1
  · push Not at hD
    obtain ⟨w, hw, C₀, hmove⟩ := hD
    exact Or.inl (R.caseB hB h5 hcat (R.outer_solvable hS hcat) hemb hw hmove)

theorem kFactLemma213Red_four (hI : GL83I294Two) (hB : SigmaCentralizerPGroup)
    (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) : KFactLemma213Red 4 :=
  kFactLemma213Red_four_of_sigma hI (Lemma213.GL83I203Sigma_of_centralizer hB) hS

theorem kFactLemma213Ge_four (hI : GL83I294Two) (hB : SigmaCentralizerPGroup)
    (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) : KFactLemma213Ge 4 :=
  (kFactLemma213Red_four hI hB hS).toGe

theorem KFactLemma213Red.of_four_le {n : ℕ} (hn : 4 ≤ n) (h : KFactLemma213Red 4) :
    KFactLemma213Red n := by
  intro p hp hp2 K _ _ hcat hcore hnc hpc P z D hconf hg hemb
  exact h p hp hp2 K hcat hcore hnc hpc P z D (hconf.mono hn) hg hemb

end CFSG.LocalAnalysis.RankFourTheoremC
