module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotientMin

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.RootSystem CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts.ChevAut
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem nodeLevi_e6 (i : Fin (Tag.rank .E6)) : NodeLevi (e6Datum K) i := by
  obtain ⟨φ, hφ, hx, hy⟩ := e6Data_valid.exists_sl2Hom K i
  exact nodeLevi_of_range_sl2 hφ (rankOne_eq_range_of_sl2
    (e6Datum_isParametrization K _ (roots_eq isFiniteType_cartan_E6)) hx hy)

theorem nodeLevi_e7 (i : Fin (Tag.rank .E7)) : NodeLevi (e7Datum K) i := by
  obtain ⟨φ, hφ, hx, hy⟩ := e7Data_valid.exists_sl2Hom K i
  exact nodeLevi_of_range_sl2 hφ (rankOne_eq_range_of_sl2
    (e7Datum_isParametrization K _ (roots_eq isFiniteType_cartan_E7)) hx hy)

end CFSG.AGLEmbeddingD2.Tits.GN516
