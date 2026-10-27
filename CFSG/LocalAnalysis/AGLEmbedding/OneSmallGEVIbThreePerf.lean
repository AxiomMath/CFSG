module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltCover
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.cover_ib_three (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3)
    {z : G} (hz : D1SmallCZElt p H R K z) (hnIa : ¬ D1SmallIa p H K)
    (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    ∃ V : Subgroup G, V ≤ H ⊓ M ∧ ⁅V, V⁆ = V ∧ z ∈ V ∧
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        V ≤ Subgroup.normalizer (L : Set G) := by
  have hzM : z ∈ M := h3.le_M hz.1
  have hz3 : z ^ 3 = 1 := by rw [← hp3, ← hz.2.1]; exact pow_orderOf_eq_one z
  have hzP : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hp : p.Prime := hp3 ▸ Nat.prime_three
  have hp2 : p ≠ 2 := by omega
  exact hd.exists_cover_blocks hz hzM hnIa hR (mem_blockNormalizer.mpr fun L hL =>
    h3.mem_normalizer_block_of_cube hp hp2 h84 h86 hD2 hzM (hp3 ▸ hzP) hz3 hCz hL)

end CFSG.AGLEmbedding
