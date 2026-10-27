module

public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ComponentClassification.BlockOverlapConjugation

theorem inf {G : Type*} [Group G] (factor overgroup : Subgroup G)
    (actor : G) (hactor : actor ∈ overgroup) :
    (factor ⊓ overgroup).map (MulAut.conj actor).toMonoidHom =
      factor.map (MulAut.conj actor).toMonoidHom ⊓ overgroup := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj actor).injective]
  have hnormalizes := (Subgroup.le_normalizer : overgroup ≤ Subgroup.normalizer (overgroup : Set G)) hactor
  rw [(CommutingComponentFamily.normalizer_iff_conjugate_eq overgroup actor).mp hnormalizes]

theorem original {G : Type*} [Group G] (component first : Subgroup G) (actor moving : G)
    (hmoving : moving ∈ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) :
    (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).map
        (MulAut.conj moving).toMonoidHom =
      UniversalOrbitBlock.conjugate first moving ⊓
        (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom :=
  inf first _ moving hmoving

theorem opposite {G : Type*} [Group G] (component second : Subgroup G) (actor moving : G)
    (hmoving : moving ∈ UniversalOrbitBlock.normalizer component) :
    (UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component).map
        (MulAut.conj moving).toMonoidHom =
      UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second actor) moving ⊓
        UniversalOrbitBlock.normalizer component :=
  inf _ _ moving hmoving

end CFSG.ComponentClassification.BlockOverlapConjugation
