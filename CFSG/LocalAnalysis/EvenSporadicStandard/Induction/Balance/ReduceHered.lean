module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Reduce
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Blueprint

open CFSG.SignalizerFunctorTheorem (IsSectionOf)

variable {H : Type} [Group H] {N : Subgroup H}

theorem catalog_of_unbalanced_of_uhered [Finite H] (hH : UHered H) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {v : H}
    (hv : orderOf v = 2) (hne : CFSG.oddCore ↥(centralizer ({v} : Set H)) ≠ ⊥) :
    CFSG.Blueprint.Catalog ↥N := by
  by_cases h2 : N.index = 2
  · exact catalog_of_index_two hN h2 hK
  · have hNtop : N = ⊤ := eq_top_of_index_ne_two hidx h2
    subst hNtop
    have := hN.isSimpleGroup
    let e : H ≃* ↥(⊤ : Subgroup H) := Subgroup.topEquiv.symm
    have : IsSimpleGroup H := e.isSimpleGroup
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    have hcat : CFSG.Blueprint.Catalog H := by
      rcases hH H (IsSectionOf.refl H) ⟨a.1, b.1, fun h => hab (Subtype.ext h)⟩ hK v hv hne with
        ⟨t, n, p, f, -, -, -, hmodel⟩ | ⟨n, h7, -, ⟨e'⟩⟩
      · exact lieModel_catalog H t n p f hmodel
      · exact Or.inr (Or.inl ⟨n, by omega, ⟨e'⟩⟩)
    exact CFSG.SectionRank.catalog_of_mulEquiv Subgroup.topEquiv hcat

end CFSG.EvenSporadicStandard.Induction.Balance
