module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Cls
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OctadIso

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster
  CFSG.Monster.ScalarKernel CFSG.Monster.Existence.Compat
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem co0ConwayFacts_of_latticeO
    (hF : Co0Facts (⊤ : Subgroup latticeO) negOneO co0C2 co0C3) : Co0ConwayFacts := by
  have hmap := Co0Facts.map (co0Equiv : latticeO →* monsterCo0) co0Equiv.injective hF
  have htop : (⊤ : Subgroup latticeO).map (co0Equiv : latticeO →* monsterCo0) = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top]
    exact co0Equiv.surjective
  rw [htop] at hmap
  have hz : (co0Equiv : latticeO →* monsterCo0) negOneO = negCo0 := co0Equiv_negOneO
  rw [hz] at hmap
  exact ⟨hmap.classify, hmap.pCore_typeC, hmap.orbit_typeC⟩

theorem co0Facts_latticeO :
    Co0Facts (⊤ : Subgroup latticeO) negOneO co0C2 co0C3 :=
  have hcls := co0ClassData
  ⟨lat_classify, lat_pCore_typeC hcls, lat_orbit_typeC hcls⟩

theorem co0ConwayFacts :
    Co0ConwayFacts :=
  co0ConwayFacts_of_latticeO co0Facts_latticeO

theorem twoCo1_not_standard_full
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Co1) : False :=
  twoCo1_not_standard octadIsolation co0ConwayFacts h h2 hQ

end CFSG.EvenSporadicStandard.TwoCo1
