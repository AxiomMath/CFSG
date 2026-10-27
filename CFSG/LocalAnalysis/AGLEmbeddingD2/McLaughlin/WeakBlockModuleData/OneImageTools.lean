module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairRankBook
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Cent
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem barM_normal_of_oneImage (hpr : AGLPair 3 M H R) (hH : Open.pRank 3 H = 2)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hr : 3 ≤ Open.pRank 3 L) : (barM M L).Normal := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  rw [← Subgroup.normalizer_eq_top_iff]
  rw [eq_top_iff]
  intro u _
  obtain ⟨⟨n, hn⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) u
  have hL' := hL.toIsTwoPrimeComponent.map_conj hn
  by_cases hLS : L.map (MulAut.conj n).toMonoidHom ≤
      Subgroup.normalizer (pCoreOf 2 H : Set G)
  · exfalso
    have hb : barM M (L.map (MulAut.conj n).toMonoidHom) ≤
        barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) := barM_mono hLS
    have hrk : Open.pRank 3 (L.map (MulAut.conj n).toMonoidHom) = Open.pRank 3 L :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 h3 _ (MulAut.conj n).injective L
    have h1 : Open.pRank 3 (barM M (L.map (MulAut.conj n).toMonoidHom)) =
        Open.pRank 3 (L.map (MulAut.conj n).toMonoidHom) :=
      pRank_barM_eq h3 (by norm_num) M _ hL'.le
    have h2 := (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hb).trans
      ((hpr.pRank_barM_normalizer_le h3 (by decide)).trans hH.le)
    omega
  · have hw : IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj n).toMonoidHom) :=
      { toIsTwoPrimeComponent := hL', not_le_normalizer := hLS }
    have h1 := hk1 _ hw
    rw [barM_map_conj hn] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1

end CFSG.AGLEmbeddingD2.McLaughlin
