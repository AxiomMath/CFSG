module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoActionFaithful
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizerJoinCommutator
public import CFSG.LocalAnalysis.ComponentClassification.SubgroupOddCoreNormalizer

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockTwoProductAction

theorem two_join {G : Type*} [Group G] (first second : Subgroup G)
    (hfirst : IsPGroup 2 first) (hsecond : IsPGroup 2 second)
    (hcommutes : ⁅first, second⁆ = ⊥) : IsPGroup 2 ↥(first ⊔ second) := by
  exact hfirst.to_sup_of_normal_left' hsecond
    ((Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes)).trans
        (Subgroup.centralizer_le_normalizer _))

theorem action {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (firstTwo secondTwo : Subgroup G)
    (hfirstTwo : IsPGroup 2 firstTwo) (hsecondTwo : IsPGroup 2 secondTwo)
    (hne : firstTwo ≠ ⊥)
    (hfirstContained : firstTwo ≤ UniversalOrbitBlock.conjugate second actor)
    (hsecondContained : secondTwo ≤ UniversalOrbitBlock.conjugate third actor)
    (hfirstNormalizes : firstTwo ≤ Subgroup.normalizer (first : Set G))
    (hsecondNormalizes : secondTwo ≤ Subgroup.normalizer (first : Set G)) :
    let acting := firstTwo ⊔ secondTwo
    let imageNormalizer := (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
    let intersection := first ⊓ imageNormalizer
    ∃ hnormalizes : acting ≤ Subgroup.normalizer (first : Set G),
      IsPGroup 2 acting ∧ acting ≠ ⊥ ∧
      acting ≤ Subgroup.normalizer (intersection : Set G) ∧ Disjoint first acting ∧
      Function.Injective ((PerfectAutomorphisms.centerQuotientHom first).comp
        (first.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes))) ∧
      (∀ member ∈ acting, member ≠ 1 → Subgroup.centralizer {member} ⊓ first ≤ intersection) ∧
      ⁅acting, intersection⁆ ≤ (componentClassificationOddCore intersection).map intersection.subtype ∧
      imageNormalizer.subgroupOf first ⊔ Subgroup.center first ≠ ⊤ := by
  let acting := firstTwo ⊔ secondTwo
  let imageNormalizer := (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let intersection := first ⊓ imageNormalizer
  have hnormalizes : acting ≤ Subgroup.normalizer (first : Set G) := sup_le hfirstNormalizes hsecondNormalizes
  have hcommutes : ⁅firstTwo, secondTwo⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    have hmap := congrArg (Subgroup.map (MulAut.conj actor).toMonoidHom)
      (UniversalOrbitBlock.block_commutes component heven huniversal second hsecond third hthird hdistinct)
    have himages : ⁅UniversalOrbitBlock.conjugate second actor,
        UniversalOrbitBlock.conjugate third actor⁆ = ⊥ := by
      change ⁅second.map (MulAut.conj actor).toMonoidHom, third.map (MulAut.conj actor).toMonoidHom⁆ = ⊥
      simpa only [Subgroup.map_commutator, Subgroup.map_bot] using hmap
    rw [← himages]
    exact Subgroup.commutator_mono hfirstContained hsecondContained
  have htwo : IsPGroup 2 acting := two_join firstTwo secondTwo hfirstTwo hsecondTwo hcommutes
  have hcontained : acting ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor :=
    sup_le (hfirstContained.trans le_sup_left) (hsecondContained.trans le_sup_right)
  have hfirstImage : UniversalOrbitBlock.conjugate second actor ≤ imageNormalizer :=
    Subgroup.map_mono ((CommutingComponentFamily.factor_le _ second hsecond).trans Subgroup.le_normalizer)
  have hsecondImage : UniversalOrbitBlock.conjugate third actor ≤ imageNormalizer :=
    Subgroup.map_mono ((CommutingComponentFamily.factor_le _ third hthird).trans Subgroup.le_normalizer)
  have hfirstIntersection : firstTwo ≤ Subgroup.normalizer (intersection : Set G) :=
    SubgroupOddCoreNormalizer.inf first imageNormalizer firstTwo hfirstNormalizes
      ((hfirstContained.trans hfirstImage).trans Subgroup.le_normalizer)
  have hsecondIntersection : secondTwo ≤ Subgroup.normalizer (intersection : Set G) :=
    SubgroupOddCoreNormalizer.inf first imageNormalizer secondTwo hsecondNormalizes
      ((hsecondContained.trans hsecondImage).trans Subgroup.le_normalizer)
  refine ⟨hnormalizes, htwo, ?_, sup_le hfirstIntersection hsecondIntersection, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hne (le_antisymm (by rw [← hbot]; exact le_sup_left) bot_le)
  · exact BlockTwoActionFaithful.disjoint_factor component heven huniversal hquasisimple hcard
      first second third hfirst hsecond hthird actor hactor acting htwo hcontained
  · exact BlockTwoActionFaithful.center_quotient_action_injective component heven huniversal hquasisimple hcard
      first second third hfirst hsecond hthird actor hactor acting htwo hcontained hnormalizes
  · intro member hmember hmemberNe central hcentral
    exact ⟨hcentral.2, BlockTwoActionFaithful.centralizer_le_image_normalizer component heven huniversal
      hquasisimple hcard second third hsecond hthird actor acting htwo hcontained member hmember hmemberNe hcentral.1⟩
  · exact NormalizerJoinCommutator.le firstTwo secondTwo intersection
      ((componentClassificationOddCore intersection).map intersection.subtype)
      (hfirstIntersection.trans (SubgroupOddCoreNormalizer.core intersection))
      (hsecondIntersection.trans (SubgroupOddCoreNormalizer.core intersection))
      (BlockMutualAction.commutator_le_core component heven huniversal hquasisimple hcard first second hfirst hsecond
        actor hactor firstTwo hfirstTwo hfirstContained hfirstNormalizes)
      (BlockMutualAction.commutator_le_core component heven huniversal hquasisimple hcard first third hfirst hthird
        actor hactor secondTwo hsecondTwo hsecondContained hsecondNormalizes)
  · exact BlockMutualAction.intersection_center_join_ne_top component heven huniversal hquasisimple hcard hcontrol
      first hfirst actor hactor

end CFSG.ComponentClassification.BlockTwoProductAction
