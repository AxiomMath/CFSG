module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Layer0Fours
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterModel

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Certified


theorem twoSuz_not_standard_of_fours {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) (h2 : Nat.card (center L) = 2)
    (hFG : CFSG.EvenSmallLie.FoursGroupCondition L) : ¬ IsSporadic (L ⧸ center L) .Suz :=
  fun hQ => twoSuz_not_standard_of_layer0
    (fun _ _ _ _ _ hs hC _ hy hy2 hyL => exists_perfect_of_outer_elt hs hC hy hy2 hyL) h h2 hQ
    (exists_layer0_of_fours h h2 hQ hFG)

end Certified

end CFSG.EvenSporadicStandard.TwoSuz
