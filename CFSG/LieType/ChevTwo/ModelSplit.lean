module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.Blueprint
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)

@[expose] def ChevTwoModelSplit : Prop :=
  ∀ (K : Type) [Group K], IsChevTwo K →
    (∃ (t : StatedLieTag) (n f : ℕ), t ≠ .Tits ∧ LieModel K t n 2 f) ∨
      (∃ n f : ℕ, LieModel K .Tits n 2 f) ∨
      Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
      StatedClassicalModel K .PSU 3 3 1

end CFSG.LieType.ChevTwo
