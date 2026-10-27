module

public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorTwoCentral
public import CFSG.LocalAnalysis.ComponentClassification.OddBlockSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CentralSylowImage

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockMovedFactorSylowCentral

theorem central {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hodd : Odd (Nat.card ↥(UniversalOrbitBlock.block component)))
    (second : Subgroup G) (hsecond : second ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmoved : ∀ first ∈ UniversalOrbitBlock.block component,
      ∃ moving ∈ first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom,
        UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second actor) moving ≠
          UniversalOrbitBlock.conjugate second actor)
    (sylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)) :
    (sylow : Subgroup ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)).map
        (UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component).subtype ≤
      (Subgroup.center (UniversalOrbitBlock.conjugate second actor)).map
        (UniversalOrbitBlock.conjugate second actor).subtype := by
  let overlap := UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component
  let acting := (sylow : Subgroup overlap).map overlap.subtype
  have htwo : IsPGroup 2 acting := sylow.isPGroup'.map overlap.subtype
  have hcontained : acting ≤ overlap := Subgroup.map_subtype_le _
  obtain ⟨first, hfirst, hfixed⟩ := OddBlockSylowAbelian.fixed_factor component heven huniversal hquasisimple hodd
    acting htwo (hcontained.trans inf_le_right)
  obtain ⟨moving, hmoving, hmovingNe⟩ := hmoved first hfirst
  exact BlockMovedFactorTwoCentral.central component heven huniversal hquasisimple hcard first second hfirst hsecond
    actor hactor moving hmoving hmovingNe acting htwo (hcontained.trans inf_le_left) hfixed

theorem unique {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hodd : Odd (Nat.card ↥(UniversalOrbitBlock.block component)))
    (second : Subgroup G) (hsecond : second ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmoved : ∀ first ∈ UniversalOrbitBlock.block component,
      ∃ moving ∈ first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom,
        UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second actor) moving ≠
          UniversalOrbitBlock.conjugate second actor)
    (firstSylow secondSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓
      UniversalOrbitBlock.normalizer component)) : firstSylow = secondSylow := by
  exact CentralSylowImage.unique _ _ inf_le_left secondSylow
    (central component heven huniversal hquasisimple hcard hodd second hsecond actor hactor hmoved secondSylow) firstSylow

theorem central_actual {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hodd : Odd (Nat.card ↥(UniversalOrbitBlock.block component)))
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (second : Subgroup G) (hsecond : second ∈ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor))
    (hmoved : ∀ first ∈ UniversalOrbitBlock.block component,
      ∃ moving ∈ first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom,
        UniversalOrbitBlock.conjugate second moving ≠ second)
    (sylow : Sylow 2 ↥(second ⊓ UniversalOrbitBlock.normalizer component)) :
    (sylow : Subgroup ↥(second ⊓ UniversalOrbitBlock.normalizer component)).map
        (second ⊓ UniversalOrbitBlock.normalizer component).subtype ≤
      (Subgroup.center second).map second.subtype := by
  obtain ⟨original, heq⟩ := (OrbitBlockConjugation.equivalence component actor).surjective ⟨second, hsecond⟩
  have hfactorEq := congrArg Subtype.val heq
  change UniversalOrbitBlock.conjugate original.val actor = second at hfactorEq
  subst second
  exact central component heven huniversal hquasisimple hcard hodd original.val original.property actor hactor hmoved sylow

end CFSG.ComponentClassification.BlockMovedFactorSylowCentral
