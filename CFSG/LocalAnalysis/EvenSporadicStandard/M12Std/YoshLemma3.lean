module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshBad

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

variable {G : Type} [Group G] {e : G}
variable (e₀ : Subgroup.centralizer ({e} : Set G) ≃*
  Multiplicative (ZMod 2) × CFSG.GH74.M12.Hyp.G12)

section Certified

set_option linter.unusedSectionVars false


theorem exists_centralSwap [Finite G] [IsSimpleGroup G] (he2 : orderOf e = 2) :
    (∃ d, CentralSwap e₀ 0 d) ∨ (∃ d, CentralSwap e₀ 1 d) := by
  rcases exists_centralSwap_or_bad e₀ he2 with h | h | ⟨d, hd, hdd, hds, hsw⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (no_bad_swap e₀ he2 hd hdd hds hsw).elim

end Certified

end CFSG.EvenSporadicStandard.M12Std.Yosh
