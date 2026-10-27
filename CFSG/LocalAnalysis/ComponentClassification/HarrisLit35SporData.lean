module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdSporadic

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup RestrictedStd RestrictedStd.Spor

structure SporCompData (s : TauCeti.SporadicName) : Prop where
  oddCore : CatalogueU.SporadicOddCoreFree s
  inner : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
    Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
      CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => ¬ SmallCentralQuotient Y
  outer : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
    Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 →
      α ∉ OuterAutomorphisms.inner G →
      CompsSatisfy (Sporadic.Schreier.fixSub α) fun Y _ => ¬ SmallCentralQuotient Y

end CFSG.ComponentClassification.HarrisLit
