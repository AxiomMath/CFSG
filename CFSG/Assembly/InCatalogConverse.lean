module

import CFSG.LieType.Catalog.Realization
public import CFSG.LieType.Simplicity.Basic
public import CFSG.Milestones.FAM_sporadic_converse
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest

public section

namespace CFSG.Assembly

theorem lie_finite_simple
    (index : TauCeti.ValidLieTypeIndex) :
    Finite index.Group ∧ IsSimpleGroup index.Group := by
  obtain ⟨t, n, r, f, -, hm, -, -, -⟩ :=
    CFSG.RankThree.PartOne.CTP.seitzBridge index.Group index.1 ⟨index.2, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨h1, -, h3⟩ := CFSG.LieType.Catalog.lieModel_finite_simple index.Group t n r f hm
  exact ⟨h1, h3⟩

theorem index_finite_simple
    : ∀ i : TauCeti.CFSGIndex, Finite i.Group ∧ IsSimpleGroup i.Group
  | .cyclic p hp => by
    obtain ⟨h1, -, h3⟩ :=
      LieType.Simplicity.fam_prime_cyclic_converse _ ⟨p, hp, ⟨MulEquiv.refl _⟩⟩
    exact ⟨h1, h3⟩
  | .alternating n hn => by
    obtain ⟨h1, -, h3⟩ :=
      LieType.Simplicity.fam_alternating_converse _ ⟨n, hn, ⟨MulEquiv.refl _⟩⟩
    exact ⟨h1, h3⟩
  | .lie index => lie_finite_simple index
  | .sporadic s => Milestones.fam_sporadic_converse_tauCeti s

open Assembly in
theorem inCatalog_converse
    (G : Type) [Group G] (h : InCatalog G) :
    Finite G ∧ IsSimpleGroup G := by
  obtain ⟨i, ⟨e⟩⟩ := h
  obtain ⟨h1, h2⟩ := index_finite_simple i
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, e.isSimpleGroup⟩

end CFSG.Assembly
