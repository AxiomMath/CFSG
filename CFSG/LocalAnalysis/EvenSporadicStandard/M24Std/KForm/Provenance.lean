module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem StdHyp.kLocalSections (h : StdHyp G L) : M24Std.KLocalSections G :=
  fun D hD hcomm =>
    (h.isKGroupCat_normalizer hD hcomm).quotient (D.subgroupOf (normalizer (D : Set G)))

end CFSG.EvenSporadicStandard
