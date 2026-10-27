module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaTransitive
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaCaseFour

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem omegaSet_eq
    (h : Setting G L D t) :
    omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t} :=
  h.omegaSet_eq_of_not_caseFour fun hiv => h.not_case_iv hiv

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
