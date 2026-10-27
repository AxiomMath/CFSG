module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.FoursModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Unconditional

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Certified


theorem twoSuz_not_standard_unconditional {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) (h2 : Nat.card (center L) = 2) : ¬ IsSporadic (L ⧸ center L) .Suz := by
  intro hQ
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.2 h.standard.1.1
  exact twoSuz_not_standard_of_fours h h2 (foursGroupCondition_of_isSporadic hperf h2 hQ) hQ

end Certified

end CFSG.EvenSporadicStandard.TwoSuz
