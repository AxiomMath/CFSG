module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Corollary
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Thompson

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem case1_final {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {M Y S U : Subgroup G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) (hSp : IsPGroup p S) (hSM : S ≤ M)
    (hF : CharTwo (Y ⊔ S)) (hperm : ∀ w ∈ Y ⊔ S, ∃ y ∈ Y, ∃ s ∈ S, w = y * s)
    (hexp : ∀ s ∈ S, s ^ p = 1) (hUS : U ≤ S) (hUc : ∀ u ∈ U, ∀ s ∈ S, u * s = s * u)
    (hUcard : Nat.card U = p ^ 2) (hSU : ¬ S ≤ U) (hUY : U ≤ normalizer (Y : Set G)) :
    normalizer (Y : Set G) ≤ M := by
  have hp : p.Prime := Fact.out
  have hprod := CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281.glauberman_Q_product p hp h5
    hY2 hSp hperm hF
  have hUA : U ≤ S ⊓ normalizer (thompsonJ Y : Set G) :=
    le_inf hUS (hUY.trans (normalizer_le_normalizer_thompsonJ' Y))
  have hUB : U ≤ S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) :=
    le_inf hUS (hUY.trans (normalizer_le_normalizer_omegaOneCenter Y))
  have hrank := three_le_pRank_of_mul hexp hUS hUc hUcard hSU inf_le_left inf_le_left hUA hUB hprod
  rcases hrank with hA3 | hB3
  · have hJ2 : IsPGroup 2 (thompsonJ Y) := hY2.to_le (thompsonJ_le_self Y)
    have hloc : IsTwoLocal (normalizer (thompsonJ Y : Set G)) :=
      ⟨thompsonJ Y, thompsonJ_ne_bot_of_two_group hY2 hY1, hJ2, rfl⟩
    have hAle : S ⊓ normalizer (thompsonJ Y : Set G) ≤ normalizer (thompsonJ Y : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hSM)
    exact (normalizer_le_normalizer_thompsonJ' Y).trans
      (hD1' _ hloc (hA3.trans (CFSG.SectionRank.pRank_mono hp.one_lt hAle)))
  · have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter Y) := hY2.to_le (omegaOneCenter_le_self Y)
    have hloc : IsTwoLocal (normalizer (quasithinOmegaOneCenter Y : Set G)) :=
      ⟨quasithinOmegaOneCenter Y, omegaOneCenter_ne_bot_of_two_group hY2 hY1, hZ2, rfl⟩
    have hBle : S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) ≤
        normalizer (quasithinOmegaOneCenter Y : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hSM)
    exact (normalizer_le_normalizer_omegaOneCenter Y).trans
      (hD1' _ hloc (hB3.trans (CFSG.SectionRank.pRank_mono hp.one_lt hBle)))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
