module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GraphOrbitDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.QuasisimpleTwoNonab

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

theorem quasisimpleModTwoNonab_iff (A : Type*) [Group A] :
    QuasisimpleModTwoNonab A ↔ IsQuasisimpleTwoNonab (A ⧸ CFSG.pCore 2 A) := Iff.rfl

theorem quasisimpleModTwoNonab_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ⧸ CFSG.pCore 2 A ≃* B) (h : IsQuasisimpleTwoNonab B) : QuasisimpleModTwoNonab A :=
  (quasisimpleModTwoNonab_iff A).2 (IsQuasisimpleTwoNonab.of_mulEquiv e.symm h)

end CFSG.AGLEmbeddingD2.Tits.GN516
