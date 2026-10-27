module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeChapterII
public import CFSG.CharacterTheory.Semidihedral.AllPrimeIVNFacts
public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Q9
public import CFSG.CharacterTheory.Semidihedral.AllPrimeFinalInputs
public import CFSG.CharacterTheory.Semidihedral.AllPrimeIV9Facts
public import CFSG.LocalAnalysis.ABGTheoremB.TheoremBStarQD

public section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion CFSG.ABGTheoremB.TotallyInverted

theorem frontier_theoremBStar_of
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hQD : (frontierSetting S fS t p f).QDBStarInputs) :
    (frontierSetting S fS t p f).TheoremBStar := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  obtain ⟨d, hdD, -, hdx₂⟩ := frontier_exists_D_swap n hn S fS t ht p f
  exact (frontierSetting S fS t p f).theoremBStar_of_qdInputs hσ rfl
    (frontier_chapterIIFacts hGnonab hrec n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel)
    (frontier_ivNFacts hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel)
    (frontier_tiFacts hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel)
    (frontier_tiFactsQ9 hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel)
    (frontier_qCoverFact hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel)
    ⟨d, hdD, hdx₂⟩ (frontier_F₀_sylow n hn S fS t ht p f)
    (frontier_h_y hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel)
    (fun _ Δ => ⟨frontier_abg_II_4_4 hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
      hq hmodel Δ, frontier_abg_II_4_10_iii hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd
      hf hq hmodel Δ⟩) hQD

end CFSG.Semidihedral.AllPrime
