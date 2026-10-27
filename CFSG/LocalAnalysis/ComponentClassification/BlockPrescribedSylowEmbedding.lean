module

public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictSylowIntersections
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionPrescribedSylowEmbedding

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockPrescribedSylowEmbedding

theorem product {G : Type*} [Group G] [Finite G]
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
    (hsecondNormalizes : secondTwo ≤ Subgroup.normalizer (first : Set G))
    (hstrict : ∀ firstSylow : Sylow 2 ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom), ∀ secondSylow : Sylow 2 first,
        Nat.card (firstSylow : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (secondSylow : Subgroup first))
    (prescribed : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    IsMulCommutative ↥(firstTwo ⊔ secondTwo) ∧
      ∃ homomorphism : ↥(firstTwo ⊔ secondTwo) →*
        Subgroup.center ((prescribed : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
            (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype),
        Function.Injective homomorphism := by
  obtain ⟨hnormalizes, htwo, _, hnormalizesIntersection, hdisjoint, _, hcentralizers, hcommutator, _⟩ :=
    BlockTwoProductAction.action component heven huniversal hquasisimple hcard hcontrol first second third
      hfirst hsecond hthird hdistinct actor hactor firstTwo secondTwo hfirstTwo hsecondTwo hne hfirstContained hsecondContained
        hfirstNormalizes hsecondNormalizes
  obtain ⟨homomorphism, hinjective⟩ := TwoActionPrescribedSylowEmbedding.embedding first (firstTwo ⊔ secondTwo)
    (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) inf_le_left htwo hdisjoint
      hnormalizes hnormalizesIntersection hcentralizers hcommutator hstrict prescribed
  exact ⟨TwoActionDisplacementEmbedding.abelian_of_embedding homomorphism hinjective, homomorphism, hinjective⟩

theorem sylow_product {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmutualEven : ∀ first ∈ UniversalOrbitBlock.block component, ∀ second ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
        Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G))))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (firstSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)))
    (secondSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)))
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom), ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (right : Subgroup first))
    (prescribed : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    let firstMutual := UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)
    let secondMutual := UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)
    let firstTwo := (firstSylow : Subgroup firstMutual).map firstMutual.subtype
    let secondTwo := (secondSylow : Subgroup secondMutual).map secondMutual.subtype
    IsMulCommutative ↥(firstTwo ⊔ secondTwo) ∧
      pRank 2 (firstTwo ⊔ secondTwo) =
        pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) ∧
      ∃ homomorphism : ↥(firstTwo ⊔ secondTwo) →*
        Subgroup.center ((prescribed : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
            (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype),
        Function.Injective homomorphism := by
  let firstMutual := UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)
  let secondMutual := UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)
  let firstTwo := (firstSylow : Subgroup firstMutual).map firstMutual.subtype
  let secondTwo := (secondSylow : Subgroup secondMutual).map secondMutual.subtype
  have hfirstLe : firstTwo ≤ firstMutual := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hsecondLe : secondTwo ≤ secondMutual := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hfirstNe : firstTwo ≠ ⊥ := by
    intro hbot
    have hcardOne := firstTwo.eq_bot_iff_card.mp hbot
    rw [Subgroup.card_map_of_injective firstMutual.subtype_injective] at hcardOne
    have hdivides := firstSylow.dvd_card_of_dvd_card
      (even_iff_two_dvd.mp (hmutualEven first hfirst second hsecond).2)
    rw [hcardOne] at hdivides
    norm_num at hdivides
  obtain ⟨hab, homomorphism, hinjective⟩ := product component heven huniversal hquasisimple hcard hcontrol
    first second third hfirst hsecond hthird hdistinct actor hactor firstTwo secondTwo
      (firstSylow.isPGroup'.map firstMutual.subtype) (secondSylow.isPGroup'.map secondMutual.subtype) hfirstNe
        (hfirstLe.trans inf_le_left) (hsecondLe.trans inf_le_left) (hfirstLe.trans inf_le_right) (hsecondLe.trans inf_le_right)
          hstrict prescribed
  have hpair := BlockPairSylowOmega.pair component heven huniversal hquasisimple hcard hcontrol actor hactor hmutualEven
    first second third hfirst hsecond hthird hdistinct firstSylow secondSylow
  exact ⟨hab, hpair.2.2, homomorphism, hinjective⟩

theorem sylow_product_omega {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (rank : ℕ) (elementary : Subgroup G)
    (properties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank elementary)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (firstSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)))
    (secondSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)))
    (hab : IsMulCommutative ↥((firstSylow : Subgroup ↥(UniversalOrbitBlock.conjugate second actor ⊓
      Subgroup.normalizer (first : Set G))).map (UniversalOrbitBlock.conjugate second actor ⊓
        Subgroup.normalizer (first : Set G)).subtype ⊔
      (secondSylow : Subgroup ↥(UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G))).map
        (UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)).subtype))
    (hrank : pRank 2 ((firstSylow : Subgroup ↥(UniversalOrbitBlock.conjugate second actor ⊓
      Subgroup.normalizer (first : Set G))).map (UniversalOrbitBlock.conjugate second actor ⊓
        Subgroup.normalizer (first : Set G)).subtype ⊔
      (secondSylow : Subgroup ↥(UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G))).map
        (UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)).subtype) = rank) :
    InvolutionGeneratedSubgroup.omega ((firstSylow : Subgroup ↥(UniversalOrbitBlock.conjugate second actor ⊓
      Subgroup.normalizer (first : Set G))).map (UniversalOrbitBlock.conjugate second actor ⊓
        Subgroup.normalizer (first : Set G)).subtype ⊔
      (secondSylow : Subgroup ↥(UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G))).map
        (UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)).subtype) = elementary := by
  let firstMutual := UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)
  let secondMutual := UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)
  let firstTwo := (firstSylow : Subgroup firstMutual).map firstMutual.subtype
  let secondTwo := (secondSylow : Subgroup secondMutual).map secondMutual.subtype
  have hcontained : ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component :=
    fun factor hfactor => properties.contained _ ((OrbitBlockConjugation.block component factor actor).mpr hfactor)
  have hnormalizes := BlockStrictSylowIntersections.right_common_normalizes component heven huniversal hcard hcontrol
    actor hactor elementary properties.isElementary hcontained first hfirst
  have helementaryMutual : elementary ≤ firstMutual :=
    le_inf ((hcontained second hsecond).trans inf_le_left) hnormalizes
  have hmutual : firstMutual ≤ UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component :=
    inf_le_inf_left _ (UniversalOrbitBlock.factor_normalizer_le component heven huniversal hquasisimple first hfirst)
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenConjugate := UniversalOrbitBlock.orbit_even component heven _ horbit
  have huniversalConjugate := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hcardConjugate : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor)) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have homega := properties.omega_subgroup hevenConjugate huniversalConjugate hcardConjugate
    (UniversalOrbitBlock.conjugate second actor) ((OrbitBlockConjugation.block component second actor).mpr hsecond)
      firstMutual helementaryMutual hmutual firstSylow
  have helementaryProduct : elementary ≤ firstTwo ⊔ secondTwo := by
    rw [← homega]
    exact (InvolutionGeneratedSubgroup.le firstTwo).trans le_sup_left
  exact InvolutionGeneratedSubgroup.eq_of_elementary_card (firstTwo ⊔ secondTwo) elementary hab properties.isElementary
    helementaryProduct (by rw [hrank]; exact properties.card)

end CFSG.ComponentClassification.BlockPrescribedSylowEmbedding
