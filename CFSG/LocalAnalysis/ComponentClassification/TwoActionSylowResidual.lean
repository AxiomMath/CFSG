module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionStrictEmbedding

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoActionSylowResidual

theorem residual {G : Type*} [Group G] [Finite G] (ambient acting intersection : Subgroup G)
    (hintersection : intersection ≤ ambient) (htwo : IsPGroup 2 acting)
    (hdisjoint : Disjoint ambient acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hcommutator : ⁅acting, intersection⁆ ≤
      (componentClassificationOddCore intersection).map intersection.subtype)
    (hfailure : ¬ IsMulCommutative acting ∨
      ¬ ∃ homomorphism : acting →* intersection, Function.Injective homomorphism) :
    ∃ first : Sylow 2 intersection, ∃ second : Sylow 2 ambient,
      let firstImage := (first : Subgroup intersection).map intersection.subtype
      let secondImage := (second : Subgroup ambient).map ambient.subtype
      firstImage = secondImage ∧ ⁅acting, secondImage⁆ = ⊥ ∧
        Subgroup.normalizer ((secondImage ⊔ acting : Subgroup G) : Set G) ⊓ ambient ≤ intersection := by
  have hnoEmbedding : ∀ fixed : Subgroup G, fixed ≤ intersection →
      ¬ ∃ homomorphism : acting →* Subgroup.center fixed, Function.Injective homomorphism := by
    intro fixed hfixed hexists
    obtain ⟨homomorphism, hinjective⟩ := hexists
    rcases hfailure with hnonabelian | hno
    · exact hnonabelian (TwoActionDisplacementEmbedding.abelian_of_embedding homomorphism hinjective)
    · apply hno
      let inclusion := (Subgroup.inclusion hfixed).comp (Subgroup.center fixed).subtype
      exact ⟨inclusion.comp homomorphism,
        ((Subgroup.inclusion_injective hfixed).comp (Subgroup.center fixed).subtype_injective).comp hinjective⟩
  obtain ⟨first, second, hle, heq, hnormalizes, hcentral⟩ := TwoActionSylowChoices.choices ambient acting intersection
    hintersection htwo hnormalizesAmbient hnormalizesIntersection hcommutator
  let firstImage := (first : Subgroup intersection).map intersection.subtype
  let secondImage := (second : Subgroup ambient).map ambient.subtype
  have hfirstIntersection : firstImage ≤ intersection := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hsecondAmbient : secondImage ≤ ambient := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hcentralizes : acting ≤ Subgroup.centralizer (firstImage : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral
  have hequal : firstImage = secondImage := by
    by_contra hne
    have hlt : firstImage < secondImage := lt_of_le_of_ne hle hne
    obtain ⟨actor, hactor, houtside, hproductNormalizes⟩ :=
      TwoActionStrictEmbedding.escape ambient acting intersection firstImage secondImage hle hsecondAmbient
        (second.isPGroup'.map ambient.subtype) htwo hdisjoint hcentralizes hnormalizes heq hlt
    exact hnoEmbedding firstImage hfirstIntersection
      (TwoActionDisplacementEmbedding.embedding ambient acting intersection firstImage
        (hfirstIntersection.trans hintersection) hdisjoint hnormalizesAmbient hcentralizes hcentralizers actor
        (hsecondAmbient hactor) houtside hproductNormalizes)
  have hsecondCentral : ⁅acting, secondImage⁆ = ⊥ := by
    change ⁅acting, firstImage⁆ = ⊥ at hcentral
    rwa [hequal] at hcentral
  refine ⟨first, second, hequal, hsecondCentral, ?_⟩
  intro actor hactor
  by_contra houtside
  apply hnoEmbedding firstImage hfirstIntersection
  apply TwoActionDisplacementEmbedding.embedding ambient acting intersection firstImage
    (hfirstIntersection.trans hintersection) hdisjoint hnormalizesAmbient hcentralizes hcentralizers actor
      hactor.2 houtside
  rw [hequal]
  exact hactor.1

end CFSG.ComponentClassification.TwoActionSylowResidual
