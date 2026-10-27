module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotient

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.RootSystem
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem nodeLevi_f4 (i : Fin (Tag.rank .F4)) : NodeLevi (f4Datum K) i := by
  obtain ⟨φ, hφ, hx, hy⟩ := Adjoint.exists_sl2_hom_xPar (K := K)
    (exists_sl2_hom (rootOperatorFamily .F4) (neighbour_F4 i).choose_spec.1)
  exact nodeLevi_of_range_sl2 hφ (rankOne_eq_range_of_sl2 (f4_isParametrization K) hx hy)

theorem nodeLevi_e8 (i : Fin (Tag.rank .E8)) : NodeLevi (e8Datum K) i := by
  obtain ⟨φ, hφ, hx, hy⟩ := Adjoint.exists_sl2_hom_xPar (K := K)
    (exists_sl2_hom (rootOperatorFamily .E8) (neighbour_E8 i).choose_spec.1)
  exact nodeLevi_of_range_sl2 hφ (rankOne_eq_range_of_sl2 (e8_isParametrization K) hx hy)

end CFSG.AGLEmbeddingD2.Tits.GN516
