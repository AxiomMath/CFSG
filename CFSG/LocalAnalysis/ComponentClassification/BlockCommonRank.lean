module

public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualNormalizers
public import CFSG.LocalAnalysis.ComponentClassification.BlockCrossRankBound
public import CFSG.LocalAnalysis.ComponentClassification.BlockExternalControlConjugation

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCommonRank

theorem equal {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmutualEven : ∀ first ∈ UniversalOrbitBlock.block component, ∀ second ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
        Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G))))
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component) :
    pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) =
      pRank 2 (UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component) := by
  have hforward := BlockCrossRankBound.bound component heven huniversal hquasisimple hcard hcontrol actor hactor
    first second hfirst hsecond (fun third hthird => (hmutualEven first hfirst third hthird).2)
  let conjugateComponent := UniversalOrbitBlock.conjugate component actor
  have hconjugateOrbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hconjugateEven := UniversalOrbitBlock.orbit_even component heven conjugateComponent hconjugateOrbit
  have hconjugateUniversal := UniversalOrbitBlock.orbit_universal component huniversal conjugateComponent hconjugateOrbit
  have hconjugateQuasisimple := UniversalOrbitBlock.orbit_quasisimple component hquasisimple conjugateComponent hconjugateOrbit
  have hconjugateCard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block conjugateComponent) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hconjugateControl := BlockExternalControlConjugation.control component actor hcontrol
  have hconjugateOutside := OrbitBlockConjugation.inverse_outside component actor hactor
  have hfirstConjugate := (OrbitBlockConjugation.block component first actor).mpr hfirst
  have hsecondConjugate := (OrbitBlockConjugation.block component second actor).mpr hsecond
  have hreverse := BlockCrossRankBound.bound conjugateComponent hconjugateEven hconjugateUniversal hconjugateQuasisimple
    hconjugateCard hconjugateControl actor⁻¹ hconjugateOutside
      (UniversalOrbitBlock.conjugate second actor) (UniversalOrbitBlock.conjugate first actor)
        hsecondConjugate hfirstConjugate (by
          intro third hthird
          let original := UniversalOrbitBlock.conjugate third actor⁻¹
          have horiginal : original ∈ UniversalOrbitBlock.block component := by
            have hmem := (OrbitBlockConjugation.block conjugateComponent third actor⁻¹).mpr hthird
            change original ∈ UniversalOrbitBlock.block
              (UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate component actor) actor⁻¹) at hmem
            rwa [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hmem
          exact (hmutualEven original horiginal second hsecond).1)
  have hnormalizer : UniversalOrbitBlock.normalizer conjugateComponent =
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom :=
    (OrbitBlockConjugation.normalizer component actor).symm
  have hnormalizerBack : (UniversalOrbitBlock.normalizer conjugateComponent).map (MulAut.conj actor⁻¹).toMonoidHom =
      UniversalOrbitBlock.normalizer component := by
    rw [OrbitBlockConjugation.normalizer]
    change UniversalOrbitBlock.normalizer
      (UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate component actor) actor⁻¹) = _
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one]
  rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one,
    hnormalizerBack, hnormalizer] at hreverse
  exact le_antisymm hreverse hforward

theorem positive {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (element : G) (helement : element ∈ BlockFusion.involutions component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (himage : (MulAut.conj actor) element ∈ UniversalOrbitBlock.normalizer component)
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component) :
    1 ≤ pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
  have hevenMutual := (BlockMutualNormalizers.even component heven huniversal hquasisimple hcard hcontrol element helement
    actor hactor himage first second hfirst hsecond).1
  have hpositive := TwoRankSylow.positive hevenMutual
  rw [TwoRankTransport.subgroup, BlockMutualRanks.left component heven huniversal hquasisimple hcard hcontrol
    first second hfirst hsecond actor hactor] at hpositive
  exact hpositive

end CFSG.ComponentClassification.BlockCommonRank
