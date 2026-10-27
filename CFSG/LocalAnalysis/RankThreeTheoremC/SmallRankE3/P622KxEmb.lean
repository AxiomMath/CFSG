module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxCfg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxEmb
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S L : Subgroup G}

namespace P622KxCfg

theorem stronglyEmbedded (hL613 : P622L613) (hp3 : p ≠ 3) (c : P622KxCfg p P M x z T S L)
    {H N : Subgroup G} (hHL : H ≤ L) (hHM : H ≤ M) (hs : S622IsSimpleSection H N) (hzH : z ∈ H)
    (hzN : z ∉ N) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) (hfd : f ∣ N.relIndex H) :
    GLBStronglyEmbedded f M := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hS := c.conf.failure.situation
  have hx := c.conf.failure.point
  have hz := c.conf.failure.central
  have hzc : ∀ g ∈ (P : Subgroup G), g * z = z * g := fun g hg =>
    mem_centralizer_iff.mp hz.centralizes g hg
  have hnpc := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.not_isPConstrained_of_section P
    c.P_le_M hz.mem hzc hz.pow_eq_one hHM hs hzH hzN
  have hpd : p ∣ N.relIndex H :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.dvd_relIndex_of_mem_sdiff hs hzH hzN hz.pow_eq_one
  exact hL613 G c.setting c.d1 c.d2 c.u0 p hp3 P M hS x z hx hz hnpc H N
    (le_inf hHM (hHL.trans c.le_C)) hs hpd f hf hf2 hfp hfd

theorem false_of_gen {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (c : P622KxCfg p P M x z T S L)
    (hU : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      4 ≤ CFSG.Open.pRank f (normalizer (U : Set G) ⊓ L)) : False := by
  obtain ⟨U, -, hU1, hU2, hrank⟩ := hU
  have hmono : CFSG.Open.pRank f (normalizer (U : Set G) ⊓ L) ≤
      CFSG.Open.pRank f (normalizer (U : Set G)) :=
    CFSG.SectionRank.pRank_mono hf.one_lt inf_le_left
  have hloc : CFSG.Open.pRank f (normalizer (U : Set G)) ≤ rankThreeLocalRank f G :=
    local_pRank_le_localRank f hf.one_lt (normalizer (U : Set G)) ⟨U, hU1, hU2, rfl⟩
  have h3 : rankThreeLocalRank f G ≤ 3 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.smallRank_localRank_le_three c.setting hf hf2
  have h4 : 4 ≤ 3 := hrank.trans (hmono.trans (hloc.trans h3))
  omega

end P622KxCfg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
