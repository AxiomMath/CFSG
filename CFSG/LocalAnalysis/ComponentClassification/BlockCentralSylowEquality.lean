module

public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowCommutation
public import CFSG.LocalAnalysis.ComponentClassification.SubgroupSylowTransport
public import CFSG.LocalAnalysis.ComponentClassification.BlockOverlapConjugation

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCentralSylowEquality

theorem original {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (first second fixed : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hfixed : fixed ∈ UniversalOrbitBlock.block component)
    (firstSylow : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom))
    (secondSylow : Sylow 2 ↥(second ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom))
    (hunique : ∀ other : Sylow 2 ↥(second ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom),
      other = secondSylow)
    (hcentral : (firstSylow : Subgroup ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
        (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype ≤
          (Subgroup.center first).map first.subtype)
    (hnormalizes : first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
      Subgroup.normalizer (UniversalOrbitBlock.conjugate fixed actor : Set G))
    (moving : G) (hmoving : moving ∈ UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component)
    (hmoved : UniversalOrbitBlock.conjugate first moving = second) :
    (firstSylow : Subgroup ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
        (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype =
      (secondSylow : Subgroup ↥(second ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
        (second ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype := by
  let firstOverlap := first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let firstTwo := (firstSylow : Subgroup firstOverlap).map firstOverlap.subtype
  have hbound : firstTwo ≤ firstOverlap := Subgroup.map_subtype_le _
  have hcentralizes := BlockCentralSylowCommutation.centralizes component heven huniversal hquasisimple hcard actor hactor
    first fixed firstTwo hfirst hfixed (firstSylow.isPGroup'.map firstOverlap.subtype) (hbound.trans inf_le_left)
      hcentral (hbound.trans hnormalizes) hmoving
  have hfixedImage : UniversalOrbitBlock.conjugate fixed actor ≤
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom :=
    Subgroup.map_mono ((CommutingComponentFamily.factor_le _ fixed hfixed).trans Subgroup.le_normalizer)
  have heq := BlockOverlapConjugation.original component first actor moving (hfixedImage hmoving.1)
  rw [hmoved] at heq
  exact SubgroupSylowTransport.unique_eq_of_centralizer _ _ moving heq firstSylow secondSylow hunique hcentralizes

theorem opposite {G : Type*} [Group G] [Finite G]
    (component first second : Subgroup G) (actor moving : G)
    (hmoving : moving ∈ UniversalOrbitBlock.normalizer component)
    (hmoved : UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate first actor) moving =
      UniversalOrbitBlock.conjugate second actor)
    (firstSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate first actor ⊓ UniversalOrbitBlock.normalizer component))
    (secondSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component))
    (hunique : ∀ other : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component),
      other = secondSylow)
    (hcentral : moving ∈ Subgroup.centralizer ((firstSylow : Subgroup ↥(UniversalOrbitBlock.conjugate first actor ⊓
      UniversalOrbitBlock.normalizer component)).map
        (UniversalOrbitBlock.conjugate first actor ⊓ UniversalOrbitBlock.normalizer component).subtype : Set G)) :
    (firstSylow : Subgroup ↥(UniversalOrbitBlock.conjugate first actor ⊓ UniversalOrbitBlock.normalizer component)).map
        (UniversalOrbitBlock.conjugate first actor ⊓ UniversalOrbitBlock.normalizer component).subtype =
      (secondSylow : Subgroup ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)).map
        (UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component).subtype := by
  have heq := BlockOverlapConjugation.opposite component first actor moving hmoving
  rw [hmoved] at heq
  exact SubgroupSylowTransport.unique_eq_of_centralizer _ _ moving heq firstSylow secondSylow hunique hcentral

end CFSG.ComponentClassification.BlockCentralSylowEquality
