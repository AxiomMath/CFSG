module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem F5Std.not_isConj (h : F5Std a z) : ¬ IsConj a z :=
  not_isConj_of_isF5Type h.iface h.typ

theorem F5Std.isConj_or_of_orderOf (h : F5Std a z) {t : G} (ht : orderOf t = 2) :
    IsConj a t ∨ IsConj z t :=
  h.loc.gzClass.self.inv_two t ht

end CFSG.EvenSporadicStandard.HNRecog.Section4
