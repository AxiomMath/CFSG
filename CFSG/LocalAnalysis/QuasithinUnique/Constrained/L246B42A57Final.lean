module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Glue

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace B42A57

theorem asB42A57_holds : AsB42A57 := by
  apply asB42A57_of_A7SixDimOff
  intro S _ _ hS G L A C hirr hA hcard
  have hS2 : ∀ s : S, s * s = 1 := fun s => by simpa [pow_two] using hS s
  have hbig : 32 ≤ Nat.card S := by
    rcases hcard with h | h <;> rw [h] <;> norm_num
  exact alternatingNatural_seven_of_offender hS2 C hirr hA hbig

end B42A57

namespace L238

variable {G : Type} [Group G] [Finite G]

theorem altBlockStatementJCat_holds
    : AltBlockStatementJCat (G := G) :=
  altBlockStatementJCat_of_asB42A57 B42A57.asB42A57_holds

end L238

end CFSG.QuasithinUnique
