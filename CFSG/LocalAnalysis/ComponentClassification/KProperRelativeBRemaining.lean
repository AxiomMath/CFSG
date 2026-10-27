module

public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieTwistedE6
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch

public section

namespace CFSG.ComponentClassification.KProperRelativeB

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.SporadicSchreierDispatch (SporadicSchreierCase)

theorem oddExceptionalFrontier_holds : OddExceptionalFrontier := by
  intro G _ _ hsimple hnonab hindex t p f ht _ hp2 hmodel hproper
  have : IsSimpleGroup (GeneralizedFitting.subgroup G) := hsimple
  exact CatalogueBOddLie.odd_E6_E7_twisted_E6_triality_B_frontier hnonab hindex t p f ht hp2
    hmodel hproper

theorem kProper_component_local_B_of_remaining
    (hTits : ∀ (S : Type) [Group S] (p f : ℕ), ReeTitsModel S .Tits p f →
      Group.IsSolvable (OuterAutomorphisms.Outer S))
    (hJ2 : SporadicSchreierCase .J2) (hJ3 : SporadicSchreierCase .J3)
    (hJ4 : SporadicSchreierCase .J4)
    (hCo1 : SporadicSchreierCase .Co1) (hCo2 : SporadicSchreierCase .Co2)
    (hCo3 : SporadicSchreierCase .Co3) (hFi22 : SporadicSchreierCase .Fi22)
    (hFi23 : SporadicSchreierCase .Fi23) (hFi24 : SporadicSchreierCase .Fi24Prime)
    (hHS : SporadicSchreierCase .HS) (hMcL : SporadicSchreierCase .McL)
    (hHe : SporadicSchreierCase .He) (hRu : SporadicSchreierCase .Ru)
    (hSuz : SporadicSchreierCase .Suz) (hON : SporadicSchreierCase .ONan)
    (hHN : SporadicSchreierCase .HN) (hLy : SporadicSchreierCase .Ly)
    (hTh : SporadicSchreierCase .Th) (hB : SporadicSchreierCase .B)
    (hM : SporadicSchreierCase .M)
    (hU : RelativeU Catalog) (hheld : HeldInput) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hK : KProper Catalog G) (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  kProper_component_local_B_of_frontiers hTits
    (fun S _ _ _ hnonab hS => SporadicSchreierDispatch.sporadicRep_schreier_of_remaining hJ2 hJ3
      hJ4 hCo1 hCo2 hCo3 hFi22 hFi23 hFi24 hHS hMcL hHe hRu hSuz hON hHN hLy hTh hB hM S hnonab
      hS)
    hU oddExceptionalFrontier_holds hheld G hK hcomp

end CFSG.ComponentClassification.KProperRelativeB
