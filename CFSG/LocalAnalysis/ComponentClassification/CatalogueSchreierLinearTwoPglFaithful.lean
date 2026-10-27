module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem pglAction_injective (K : Type*) [Field K] [Finite K] :
    Function.Injective (pglAction K) := by
  intro g h hgh
  have h1 : semilinearAction K (SemidirectProduct.inl g) =
      semilinearAction K (SemidirectProduct.inl h) := by
    rw [semilinearAction_inl, semilinearAction_inl, hgh]
  exact SemidirectProduct.inl_injective (semilinearAction_injective K h1)

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
