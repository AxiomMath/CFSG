module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeSetting
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierGaps

public section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups

theorem stationaryCoverageStatement_of_theoremBStar
    (hB : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
      ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
        (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
      ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
        (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
        Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
        (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
      ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
        CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
        (frontierSetting S fS t p f).TheoremBStar) :
    SimpleLayerFrontier.StationaryCoverageStatement := by
  intro G _ _ _ hGnonab hrec n hn S fS t ht _ hnonab hcentral hnc p f hp hpodd hf hq hmodel
  exact allLocalPrimeStationaryCovers_of_allLocalPrimesOrdinary hGnonab hrec n hn S fS t ht
    hnonab hcentral hnc p f hp hpodd hf hq.le hmodel
    (allLocalPrimesOrdinary_of_theoremBStar hn S fS t ht p f
      (hB G hGnonab hrec n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel))

end CFSG.Semidihedral.AllPrime
