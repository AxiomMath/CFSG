module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RJr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t : G} {P U : Subgroup G}

theorem Wr7.normalizer_star_le (h : Wr7 t P U) (hU : RankFacts U) :
    ∀ x ∈ normalizer ((wrStar t P : Subgroup G) : Set G), x ∈ normalizer (P : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  let f : G →* G := MulAut.conj x
  have hx' : (wrStar t P).map f = wrStar t P := hx
  have hmap := thompsonRank_map (f := f) (MulAut.conj x).injective (wrStar t P)
  rw [hx', Wr7.thompsonRank_star h hU] at hmap
  simpa [f] using hmap.symm

end CFSG.OddStandard.HigherRank.YamadaG23
