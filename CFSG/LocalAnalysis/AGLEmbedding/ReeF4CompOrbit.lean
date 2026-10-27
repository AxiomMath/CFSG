module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4CompRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Comp2

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R X : Subgroup G}

theorem D1ReeF4Data.orbit_le (h : D1ReeF4Data P M H R X)
    (hind : ∀ q ∈ GLBBetaFour G, q < 5 → D1At G q) (hRank : StmtComponentRank)
    (hLift : StmtBarPRankLift) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    {y l : ↥M ⧸ CFSG.pCore 2 ↥M} (hyL : y ∈ Lb) (hyK : y ∈ barM M (H ⊓ M))
    (hy3 : IsPGroup 3 (Subgroup.zpowers y)) (hlL : l ∈ Lb) (hyl : y * l ≠ l * y)
    {m : ℕ} (g : Fin m → ↥M ⧸ CFSG.pCore 2 ↥M) (hg : ∀ j, g j ∈ barM M (H ⊓ M))
    (hinj : Function.Injective fun j => Lb.map (MulAut.conj (g j)).toMonoidHom) : m ≤ 3 :=
  (le_pRank_of_injective_conj' hRank hLift inf_le_right Nat.prime_three (by norm_num) hLb hyK
    hyL hy3 hlL hyl g hg hinj).trans (h.pRank_three_le hind)

end Comp2

end CFSG.AGLEmbedding
