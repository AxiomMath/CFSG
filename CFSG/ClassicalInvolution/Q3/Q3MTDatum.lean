module

public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.ULieType

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform

section Datum

variable {G : Type} [Group G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ}


theorem exists_datum_of_hasLieTypeU (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hne : Ω.Nonempty)
    (h : HasLieTypeU 3 1 Ω t k) : ∃ e, Nonempty (Ih8Model 3 1 Ω t k e) := by
  obtain ⟨D, hcard, i, e, he, ht, hadm, hc⟩ := h
  exact ⟨e, ⟨D.toIh8Model hΩ hne hcard i ht hadm he hc⟩⟩

end Datum

end CFSG.ClassicalInvolution.Q3.Q3MT
