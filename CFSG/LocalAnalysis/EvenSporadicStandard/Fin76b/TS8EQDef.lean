module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13EDef

public section

namespace CFSG.EvenSporadicStandard.Fin76b

structure EFactsQ {G : Type*} [Group G] (E : Subgroup G) (t : G) : Prop where
  common_invol : ∀ a ∈ innAutE E, ∀ b ∈ innAutE E,
    ∃ c : MulAut ↥E, c ∉ innAutE E ∧ c * c = 1 ∧ c * a = a * c ∧ c * b = b * c

end CFSG.EvenSporadicStandard.Fin76b
