module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoActionFaithful
public import CFSG.LocalAnalysis.ComponentClassification.ConjugationPairStabilizer
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionOddStabilizerEmbedding

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockOddPairOrbitEmbedding

theorem product_normalizes_factors {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component) (hdistinct : first ≠ second)
    (actor : G) :
    UniversalOrbitBlock.conjugate first actor ⊔ UniversalOrbitBlock.conjugate second actor ≤
      Subgroup.normalizer (UniversalOrbitBlock.conjugate first actor : Set G) ⊓
        Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G) := by
  have hcommutes := UniversalOrbitBlock.block_commutes component heven huniversal first hfirst second hsecond hdistinct
  have himages : ⁅UniversalOrbitBlock.conjugate first actor, UniversalOrbitBlock.conjugate second actor⁆ = ⊥ := by
    change ⁅first.map (MulAut.conj actor).toMonoidHom, second.map (MulAut.conj actor).toMonoidHom⁆ = ⊥
    have hmap := congrArg (Subgroup.map (MulAut.conj actor).toMonoidHom) hcommutes
    simpa only [Subgroup.map_commutator, Subgroup.map_bot] using hmap
  have hfirstCentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp himages
  have hsecondCentral := Subgroup.le_centralizer_iff.mp hfirstCentral
  apply le_inf
  · exact sup_le Subgroup.le_normalizer (hsecondCentral.trans (Subgroup.centralizer_le_normalizer _))
  · exact sup_le (hfirstCentral.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer

theorem embedding {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (acting : Subgroup G) (htwo : IsPGroup 2 acting)
    (hcontained : acting ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (hnormalizes : acting ≤ Subgroup.normalizer (first : Set G))
    (hoddOrbit : Odd (Nat.card ↥(ConjugationPairStabilizer.orbit
      (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
        (UniversalOrbitBlock.conjugate second actor) (UniversalOrbitBlock.conjugate third actor))))
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom), ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (right : Subgroup first))
    (prescribed : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    IsMulCommutative acting ∧
      ∃ homomorphism : acting →*
        Subgroup.center ((prescribed : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
            (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype),
        Function.Injective homomorphism := by
  let oppositeFirst := UniversalOrbitBlock.conjugate second actor
  let oppositeSecond := UniversalOrbitBlock.conjugate third actor
  let opposite := oppositeFirst ⊔ oppositeSecond
  let imageNormalizer := (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let intersection := first ⊓ imageNormalizer
  let localStabilizer := ConjugationPairStabilizer.stabilizer intersection oppositeFirst oppositeSecond
  let stabilizer := localStabilizer.map intersection.subtype
  have hstabilizer : stabilizer ≤ intersection := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hstabilizerIndex : Odd (stabilizer.subgroupOf intersection).index := by
    have heq : stabilizer.subgroupOf intersection = localStabilizer :=
      Subgroup.comap_map_eq_self_of_injective intersection.subtype_injective _
    rw [heq]
    exact ConjugationPairStabilizer.odd_index intersection oppositeFirst oppositeSecond hoddOrbit
  have hactingNormalizer : acting ≤ imageNormalizer := hcontained.trans (sup_le
    (Subgroup.map_mono ((CommutingComponentFamily.factor_le _ second hsecond).trans Subgroup.le_normalizer))
    (Subgroup.map_mono ((CommutingComponentFamily.factor_le _ third hthird).trans Subgroup.le_normalizer)))
  have hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G) :=
    SubgroupOddCoreNormalizer.inf first imageNormalizer acting hnormalizes (hactingNormalizer.trans Subgroup.le_normalizer)
  have hfactors := hcontained.trans (product_normalizes_factors component heven huniversal second third hsecond hthird
    hdistinct actor)
  have hnormalizedStabilizer : acting ≤ Subgroup.normalizer (stabilizer : Set G) :=
    ConjugationPairStabilizer.normalized intersection oppositeFirst oppositeSecond acting hnormalizesIntersection
      (hfactors.trans inf_le_left) (hfactors.trans inf_le_right)
  have hoddIntersection : Odd (Nat.card ↥(first ⊓ opposite)) := by
    simpa only [sup_idem] using BlockProductFusion.intersection_odd component heven huniversal hquasisimple hcard
      first first second third hfirst hfirst hsecond hthird actor hactor
  have hdisjoint := BlockTwoActionFaithful.disjoint_factor component heven huniversal hquasisimple hcard
    first second third hfirst hsecond hthird actor hactor acting htwo hcontained
  have hcentralizers : ∀ member ∈ acting, member ≠ 1 → Subgroup.centralizer {member} ⊓ first ≤ intersection := by
    intro member hmember hne
    exact le_inf inf_le_right (inf_le_left.trans
      (BlockTwoActionFaithful.centralizer_le_image_normalizer component heven huniversal hquasisimple hcard
        second third hsecond hthird actor acting htwo hcontained member hmember hne))
  obtain ⟨homomorphism, hinjective⟩ := TwoActionOddStabilizerEmbedding.embedding first opposite acting intersection stabilizer
    inf_le_left hstabilizer hstabilizerIndex htwo hcontained hoddIntersection hdisjoint hnormalizes hnormalizedStabilizer
      (ConjugationPairStabilizer.pair_normalizes_product intersection oppositeFirst oppositeSecond) hcentralizers hstrict prescribed
  exact ⟨TwoActionDisplacementEmbedding.abelian_of_embedding homomorphism hinjective, homomorphism, hinjective⟩

end CFSG.ComponentClassification.BlockOddPairOrbitEmbedding
