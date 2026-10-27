module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.QuasithinUnique.K1.SporadicPerm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tab_eq_of_rep (T : Table) (g : Γ) (h : Rep n T g) :
    tab n g = (List.range n).map (ap T) := by
  apply List.ext_getElem
  · simp [tab]
  · intro i h1 h2
    have hi : i < n := by simpa [tab] using h1
    have := (h i hi).trans (idx_of_lt g hi)
    simp only [tab, List.getElem_map, List.getElem_finRange, List.getElem_range]
    exact this.symm

end CFSG.QuasithinUnique.K1.SporadicPerm
