module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X]

@[expose] def gnStab (T : Subgroup X) (N : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  T ⊓ N.comap (QuotientGroup.mk' (gnC T))

theorem gnStab_le (T : Subgroup X) (N : Subgroup (X ⧸ gnC T)) : gnStab T N ≤ T := inf_le_left

theorem mem_gnStab {T : Subgroup X} {N : Subgroup (X ⧸ gnC T)} {x : X} :
    x ∈ gnStab T N ↔ x ∈ T ∧ QuotientGroup.mk' (gnC T) x ∈ N :=
  Iff.rfl

end CFSG.AGLEmbeddingD2.Tits.GN516
