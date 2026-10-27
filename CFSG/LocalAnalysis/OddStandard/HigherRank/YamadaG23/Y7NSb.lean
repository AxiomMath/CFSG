module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7SFc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSigA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem sgFacts_of_setting {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hgσ : ActsAs L g s.fr'.σ) : SgFacts s.fr.S s.fr.F g := by
  have hgsn := s3_g_normalizes_S hH.hS hH.hZ s hgσ
  refine sgFacts_of_frame (frameWith s g) (s3_rankFacts hH)
    (s3_isE3_F hH.hS hH.hZ hH.hOut s) (hH.hLF.sigma g hg2 hgσ).1 hg2 ?_ ?_
  · change g ∉ s.fr.S
    intro hgS
    exact s3_mul_g_not_mem_L hH.hS hH.hOut s hgσ (y := 1) (one_mem L)
      (by simpa using s3_S_le_L s hgS)
  · intro x hx
    exact (Subgroup.mem_set_normalizer_iff.mp hgsn x).mp hx

end CFSG.OddStandard.HigherRank.YamadaG23
