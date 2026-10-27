module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeCenter
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Lattice

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbCubeConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem lattice (hc : D1IbCubeConfig p P M H R Rbar K z) (hShape : KFactSmallSylowShape)
    (hOrb3 : KFactSmallOrbitsCube) {B : Subgroup G} (hBR : B ≤ R) (hB : IsInvR p H R K z B) :
    d1LiftX p H R K ≤ B ∨
      ((∀ b ∈ B, ∃ c ∈ centerOf (d1LiftX p H R K), ∃ i : ℕ, b = c * z ^ i) ∧
        (B ⊓ d1LiftX p H R K = ⊥ → B ≤ Subgroup.zpowers z) ∧
        (B ⊓ d1LiftX p H R K ≠ ⊥ → centerOf (d1LiftX p H R K) ≤ B)) :=
  hc.toThreeData.lattice hShape hOrb3 hBR hB

end D1IbCubeConfig

end CFSG.AGLEmbedding
