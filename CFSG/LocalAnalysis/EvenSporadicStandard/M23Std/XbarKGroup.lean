module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

theorem Setup.isKGroupCat_xbar (S : Setup L z t F L1 N) (h : StdHyp G L) :
    CFSG.SectionRank.IsKGroupCat (Xbar L1) := by
  have hne : L1 ≠ ⊥ := fun h0 => by
    have := S.L1_card
    rw [h0, Subgroup.card_bot] at this
    omega
  exact (h.isKGroupCat_normalizer hne S.L1_comm).quotient _

end CFSG.EvenSporadicStandard.M23Std
