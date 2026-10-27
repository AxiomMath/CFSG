module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem quotModIso_relIndex_eq {X W N Q Z : Subgroup G} (h : QuotModIso X W N Q Z) :
    N.relIndex W = Z.relIndex Q := by
  unfold QuotModIso SecProp at h
  obtain ⟨hZ, hN, φ, -⟩ := h
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  exact Nat.card_congr φ.toEquiv

end CFSG.OddStandard.HigherRank.YamadaG23
