module

public import CFSG.LocalAnalysis.ComponentClassification.BlockExternalInvolution
public import CFSG.LocalAnalysis.ComponentClassification.BlockFactorInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.BlockFactorContainment

@[expose] def ExternalControl {G : Type*} [Group G] (component : Subgroup G) : Prop :=
  ∀ member ∈ BlockFusion.involutions component, ∀ actor : G,
    actor ∉ UniversalOrbitBlock.normalizer component →
    (MulAut.conj actor) member ∈ UniversalOrbitBlock.normalizer component →
    ∀ factor ∈ UniversalOrbitBlock.block component,
      UniversalOrbitBlock.conjugate factor ((MulAut.conj actor) member) = factor

theorem external_control_of_local_solvability {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component)) (hB : LocalB.LocalBProperty G)
    (hcore : ∀ element : G, orderOf element = 2 →
      Group.IsSolvable (componentClassificationOddCore (Subgroup.centralizer {element})))
    (houter : ∀ element : G, orderOf element = 2 →
      ∀ factor : Subgroup ((Subgroup.centralizer {element}) ⧸
        componentClassificationOddCore (Subgroup.centralizer {element})),
        IsComponentOf factor ⊤ → factor ≠ ⊤ →
          Group.IsSolvable (OuterAutomorphisms.Outer (factor ⧸ Subgroup.center factor))) :
    ExternalControl component := by
  intro member hmember actor hactor himage
  have horder : orderOf ((MulAut.conj actor) member) = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective member).trans hmember.1
  let : Group.IsSolvable (componentClassificationOddCore (Subgroup.centralizer {(MulAut.conj actor) member})) :=
    hcore _ horder
  exact BlockExternalInvolution.fixes_factors component heven huniversal hquasisimple hcard hB
    member hmember actor hactor himage (houter _ horder)

theorem reverse_normalizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcontrol : ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (member : G) (hmember : member ∈ BlockFusion.involutions component)
    (himageNormalizer : member ∈ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) :
    member ∈ Subgroup.normalizer (UniversalOrbitBlock.conjugate factor actor : Set G) := by
  have hactorInverse : actor⁻¹ ∉ UniversalOrbitBlock.normalizer component :=
    fun hmem => hactor ((UniversalOrbitBlock.normalizer component).inv_mem_iff.mp hmem)
  have hpreimage : (MulAut.conj actor⁻¹) member ∈ UniversalOrbitBlock.normalizer component := by
    obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp himageNormalizer
    have hidentity : (MulAut.conj actor⁻¹) ((MulAut.conj actor) original) = original := by
      simp only [MulAut.conj_apply, inv_inv]
      group
    rw [← heq]
    change (MulAut.conj actor⁻¹) ((MulAut.conj actor) original) ∈ UniversalOrbitBlock.normalizer component
    rwa [hidentity]
  have hfixed := hcontrol member hmember actor⁻¹ hactorInverse hpreimage factor hfactor
  have hnormalizes : (MulAut.conj actor⁻¹) member ∈ Subgroup.normalizer (factor : Set G) :=
    (CommutingComponentFamily.normalizer_iff_conjugate_eq factor _).mpr hfixed
  have himage := Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom hnormalizes
  rw [Subgroup.map_normalizer_eq_of_bijective factor (MulAut.conj actor).bijective] at himage
  have hidentity : (MulAut.conj actor) ((MulAut.conj actor⁻¹) member) = member := by
    simp only [MulAut.conj_apply, inv_inv]
    group
  change (MulAut.conj actor) ((MulAut.conj actor⁻¹) member) ∈
    Subgroup.normalizer (UniversalOrbitBlock.conjugate factor actor : Set G) at himage
  rwa [hidentity] at himage

theorem image_centralizer_le {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component) (actor : G)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (member : G) (hmember : member ∈ UniversalOrbitBlock.conjugate factor actor)
    (horder : orderOf member = 2) (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component)) :
    Subgroup.centralizer {member} ≤
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom := by
  obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hmember
  have horiginalOrder : orderOf original = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
      ((congrArg orderOf heq).trans horder)
  have horiginalFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard
    factor hfactor original horiginal horiginalOrder
  obtain ⟨_, other, hother, hcentralizes⟩ := horiginalFusion
  have hle := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
    (UniversalOrbitBlock.involution_centralizer_le component heven huniversal hquasisimple other hother
      original horiginalOrder hcentralizes)
  rw [UniversalComponentBlock.singleton_centralizer_map] at hle
  have heq' : (MulAut.conj actor) original = member := heq
  rwa [heq'] at hle

theorem image_involution_controls {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : ExternalControl component) (actor : G)
    (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (himageLe : UniversalOrbitBlock.conjugate factor actor ≤ UniversalOrbitBlock.normalizer component)
    (member : G) (hmember : member ∈ UniversalOrbitBlock.conjugate factor actor)
    (horder : orderOf member = 2) :
    ∀ other ∈ UniversalOrbitBlock.block component, member ∈ Subgroup.normalizer (other : Set G) := by
  obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hmember
  have horiginalOrder : orderOf original = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
      ((congrArg orderOf heq).trans horder)
  have horiginalFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard
    factor hfactor original horiginal horiginalOrder
  intro other hother
  have hmemberNormalizer : (MulAut.conj actor) original ∈ UniversalOrbitBlock.normalizer component := by
    have hmem : (MulAut.conj actor) original ∈ UniversalOrbitBlock.conjugate factor actor :=
      Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom horiginal
    exact himageLe hmem
  have hfixed := hcontrol original horiginalFusion actor hactor hmemberNormalizer other hother
  have heq' : (MulAut.conj actor) original = member := heq
  rw [heq'] at hfixed
  exact (CommutingComponentFamily.normalizer_iff_conjugate_eq other member).mpr hfixed

theorem image_normalizes_factors {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : ExternalControl component) (actor : G)
    (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (himageLe : UniversalOrbitBlock.conjugate factor actor ≤ UniversalOrbitBlock.normalizer component) :
    ∀ other ∈ UniversalOrbitBlock.block component,
      UniversalOrbitBlock.conjugate factor actor ≤ Subgroup.normalizer (other : Set G) := by
  classical
  let image := UniversalOrbitBlock.conjugate factor actor
  let normalizer := UniversalOrbitBlock.normalizer component
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  have himageEven : Even (Nat.card image) := by
    change Even (Nat.card (factor.map (MulAut.conj actor).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective]
    exact UniversalOrbitBlock.orbit_even component heven factor hfactor.1
  obtain ⟨imageInvolution, himageOrder⟩ := exists_prime_orderOf_dvd_card' (G := image) 2
    (even_iff_two_dvd.mp himageEven)
  have hinvolutionOrder : orderOf imageInvolution.val = 2 :=
    (orderOf_injective image.subtype image.subtype_injective imageInvolution).trans himageOrder
  intro other hother
  have hinvolutionNormalizes := image_involution_controls component heven huniversal hcard hcontrol actor hactor
    factor hfactor himageLe imageInvolution.val imageInvolution.property hinvolutionOrder other hother
  let automorphism : MulAut other :=
    (MulAut.conj imageInvolution.val).subgroupMap other |>.trans
      (MulEquiv.subgroupCongr
        ((CommutingComponentFamily.normalizer_iff_conjugate_eq other imageInvolution.val).mp hinvolutionNormalizes))
  have hinvolutionSquare : imageInvolution.val * imageInvolution.val = 1 := by
    rw [← pow_two, ← hinvolutionOrder]
    exact pow_orderOf_eq_one imageInvolution.val
  have hautomorphism : Function.Involutive automorphism := by
    intro member
    apply Subtype.ext
    change imageInvolution.val * (imageInvolution.val * member.val * imageInvolution.val⁻¹) * imageInvolution.val⁻¹ = member.val
    have hinverse := inv_eq_self_of_orderOf_eq_two hinvolutionOrder
    rw [hinverse]
    calc
      imageInvolution.val * (imageInvolution.val * member.val * imageInvolution.val) * imageInvolution.val =
          (imageInvolution.val * imageInvolution.val) * member.val * (imageInvolution.val * imageInvolution.val) := by group
      _ = member.val := by rw [hinvolutionSquare]; group
  obtain ⟨fixedInvolution, hfixedOrder, hfixed⟩ := InvolutionFixedPoints.exists_fixed_involution
    (even_iff_two_dvd.mp (UniversalOrbitBlock.orbit_even component heven other hother.1)) automorphism hautomorphism
  have hfixedAmbientOrder : orderOf fixedInvolution.val = 2 :=
    (orderOf_injective other.subtype other.subtype_injective fixedInvolution).trans hfixedOrder
  have hfixedFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard other hother
    fixedInvolution.val fixedInvolution.property hfixedAmbientOrder
  have hfixedCentralizer : fixedInvolution.val ∈ Subgroup.centralizer {imageInvolution.val} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have heq := congrArg Subtype.val hfixed
    change imageInvolution.val * fixedInvolution.val * imageInvolution.val⁻¹ = fixedInvolution.val at heq
    calc
      fixedInvolution.val * imageInvolution.val =
          (imageInvolution.val * fixedInvolution.val * imageInvolution.val⁻¹) * imageInvolution.val := by rw [heq]
      _ = imageInvolution.val * fixedInvolution.val := by group
  have hfixedImageNormalizer := image_centralizer_le component heven huniversal hquasisimple actor factor hfactor
    imageInvolution.val imageInvolution.property hinvolutionOrder hcard hfixedCentralizer
  have hfixedNormalizesImage := reverse_normalizes component hcontrol actor hactor factor hfactor
    fixedInvolution.val hfixedFusion hfixedImageNormalizer
  by_contra hnotNormalizes
  let proper := (Subgroup.normalizer (other : Set G)).subgroupOf image
  have hproper : proper ≠ ⊤ := by
    intro heq
    apply hnotNormalizes
    intro member hmember
    have hmem : (⟨member, hmember⟩ : image) ∈ proper := by rw [heq]; exact Subgroup.mem_top _
    exact hmem
  have houtsideCentralizes : ∀ member : image, member ∉ proper →
      member ∈ (Subgroup.centralizer {fixedInvolution.val}).subgroupOf image := by
    intro member houtside
    have hconjugate := (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple
      member.val).mp (himageLe member.property) other hother
    have hconjugateNe : other ≠ UniversalOrbitBlock.conjugate other member.val := by
      intro heq
      apply houtside
      exact (CommutingComponentFamily.normalizer_iff_conjugate_eq other member.val).mpr heq.symm
    have hcommutes := UniversalOrbitBlock.block_commutes component heven huniversal other hother
      (UniversalOrbitBlock.conjugate other member.val) hconjugate hconjugateNe
    let conjugateInvolution := (MulAut.conj member.val) fixedInvolution.val
    let displacement := conjugateInvolution * fixedInvolution.val
    have hconjugateMem : conjugateInvolution ∈ UniversalOrbitBlock.conjugate other member.val :=
      Subgroup.mem_map_of_mem (MulAut.conj member.val).toMonoidHom fixedInvolution.property
    have hdisplacementCommute : Commute conjugateInvolution fixedInvolution.val :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes fixedInvolution.property)
        conjugateInvolution hconjugateMem
    have hfixedSquare : fixedInvolution.val ^ 2 = 1 := by rw [← hfixedAmbientOrder]; exact pow_orderOf_eq_one _
    have hconjugateSquare : conjugateInvolution ^ 2 = 1 := by
      change ((MulAut.conj member.val) fixedInvolution.val) ^ 2 = 1
      rw [← map_pow, hfixedSquare, map_one]
    have hdisplacementSquare : displacement ^ 2 = 1 := by
      rw [hdisplacementCommute.mul_pow, hconjugateSquare, hfixedSquare, one_mul]
    have hdisplacementImage : displacement ∈ image := by
      have hconjugateMember : fixedInvolution.val * member.val⁻¹ * fixedInvolution.val⁻¹ ∈ image :=
        (Subgroup.mem_normalizer_iff.mp hfixedNormalizesImage member.val⁻¹).mp (image.inv_mem member.property)
      have hinverse := inv_eq_self_of_orderOf_eq_two hfixedAmbientOrder
      change member.val * fixedInvolution.val * member.val⁻¹ * fixedInvolution.val ∈ image
      simpa only [hinverse, mul_assoc] using image.mul_mem member.property hconjugateMember
    have hdisplacementOne : displacement = 1 := by
      by_contra hne
      have hdisplacementOrder : orderOf displacement = 2 := orderOf_eq_prime hdisplacementSquare hne
      have hdisplacementProduct : displacement ∈ other ⊔ UniversalOrbitBlock.conjugate other member.val := by
        rw [sup_comm]
        exact Subgroup.mul_mem_sup hconjugateMem fixedInvolution.property
      let firstIndex : Index := ⟨other, hother⟩
      let secondIndex : Index := ⟨UniversalOrbitBlock.conjugate other member.val, hconjugate⟩
      obtain ⟨third, hthirdFirst, hthirdSecond⟩ := ComponentFamilyPumpUpFusion.exists_outside_two
        hfamilyCard firstIndex secondIndex
      have hproductCentralizes : other ⊔ UniversalOrbitBlock.conjugate other member.val ≤
          Subgroup.centralizer (third.val : Set G) := by
        apply sup_le
        · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (UniversalOrbitBlock.block_commutes component heven huniversal other hother third.val third.property
              (fun heq => hthirdFirst (Subtype.ext heq.symm)))
        · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (UniversalOrbitBlock.block_commutes component heven huniversal
              (UniversalOrbitBlock.conjugate other member.val) hconjugate third.val third.property
              (fun heq => hthirdSecond (Subtype.ext heq.symm)))
      obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hdisplacementImage
      have horiginalOrder : orderOf original = 2 :=
        (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
          ((congrArg orderOf heq).trans hdisplacementOrder)
      have horiginalFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard
        factor hfactor original horiginal horiginalOrder
      obtain ⟨_, imageOther, himageOther, himageOtherCentral⟩ := horiginalFusion
      have hnormalizes := BlockFusion.common_involution_forces_normalizer component heven huniversal hquasisimple
        imageOther third.val himageOther third.property actor displacement hdisplacementOrder
        (by
          have hcentral := UniversalComponentBlock.centralizing_image (MulAut.conj actor) imageOther original
            himageOtherCentral
          have heq' : (MulAut.conj actor) original = displacement := heq
          rwa [heq'] at hcentral)
        (hproductCentralizes hdisplacementProduct)
      exact hactor hnormalizes
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hconjugateEq : conjugateInvolution = fixedInvolution.val := by
      have heq := mul_eq_one_iff_eq_inv.mp hdisplacementOne
      exact heq.trans (inv_eq_self_of_orderOf_eq_two hfixedAmbientOrder)
    change member.val * fixedInvolution.val = fixedInvolution.val * member.val
    calc
      member.val * fixedInvolution.val = (member.val * fixedInvolution.val * member.val⁻¹) * member.val := by group
      _ = fixedInvolution.val * member.val := by rw [show member.val * fixedInvolution.val * member.val⁻¹ =
        fixedInvolution.val from hconjugateEq]
  have hcentralizerTop := BlockFactorInvolutions.complement_le proper
    ((Subgroup.centralizer {fixedInvolution.val}).subgroupOf image) hproper houtsideCentralizes
  have hfixedCentralizesImage : fixedInvolution.val ∈ Subgroup.centralizer (image : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have hcentral : (⟨member, hmember⟩ : image) ∈ (Subgroup.centralizer {fixedInvolution.val}).subgroupOf image := by
      rw [hcentralizerTop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_centralizer_singleton_iff.mp hcentral
  obtain ⟨_, centralizedFactor, hcentralizedFactor, hcentralized⟩ := hfixedFusion
  exact hactor (BlockFusion.common_involution_forces_normalizer component heven huniversal hquasisimple
    factor centralizedFactor hfactor hcentralizedFactor actor fixedInvolution.val hfixedAmbientOrder
    hfixedCentralizesImage hcentralized)

theorem transporter {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : ExternalControl component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (actor : G)
    (himageLe : UniversalOrbitBlock.conjugate factor actor ≤ UniversalOrbitBlock.normalizer component) :
    actor ∈ UniversalOrbitBlock.normalizer component := by
  by_contra hactor
  let image := UniversalOrbitBlock.conjugate factor actor
  have himageEven : Even (Nat.card image) := by
    change Even (Nat.card (factor.map (MulAut.conj actor).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective]
    exact UniversalOrbitBlock.orbit_even component heven factor hfactor.1
  have himageQuasi : IsQuasisimple image := UniversalOrbitBlock.orbit_quasisimple component hquasisimple
    image (UniversalOrbitBlock.orbit_conjugate component factor hfactor.1 actor)
  have himageNormalizes := image_normalizes_factors component heven huniversal hquasisimple hcard hcontrol
    actor hactor factor hfactor himageLe
  have hfactorNormalizes := himageNormalizes factor hfactor
  obtain ⟨imageInvolution, himageOrder⟩ := exists_prime_orderOf_dvd_card' (G := image) 2
    (even_iff_two_dvd.mp himageEven)
  have hinvolutionOrder : orderOf imageInvolution.val = 2 :=
    (orderOf_injective image.subtype image.subtype_injective imageInvolution).trans himageOrder
  let factorAutomorphism : MulAut factor :=
    (MulAut.conj imageInvolution.val).subgroupMap factor |>.trans
      (MulEquiv.subgroupCongr ((CommutingComponentFamily.normalizer_iff_conjugate_eq factor imageInvolution.val).mp
        (hfactorNormalizes imageInvolution.property)))
  have hinvolutionSquare : imageInvolution.val * imageInvolution.val = 1 := by
    rw [← pow_two, ← hinvolutionOrder]
    exact pow_orderOf_eq_one imageInvolution.val
  have hautomorphism : Function.Involutive factorAutomorphism := by
    intro member
    apply Subtype.ext
    change imageInvolution.val * (imageInvolution.val * member.val * imageInvolution.val⁻¹) * imageInvolution.val⁻¹ = member.val
    rw [inv_eq_self_of_orderOf_eq_two hinvolutionOrder]
    calc
      imageInvolution.val * (imageInvolution.val * member.val * imageInvolution.val) * imageInvolution.val =
          (imageInvolution.val * imageInvolution.val) * member.val * (imageInvolution.val * imageInvolution.val) := by group
      _ = member.val := by rw [hinvolutionSquare]; group
  obtain ⟨fixedInvolution, hfixedOrder, hfixed⟩ := InvolutionFixedPoints.exists_fixed_involution
    (even_iff_two_dvd.mp (UniversalOrbitBlock.orbit_even component heven factor hfactor.1))
    factorAutomorphism hautomorphism
  have hfixedAmbientOrder : orderOf fixedInvolution.val = 2 :=
    (orderOf_injective factor.subtype factor.subtype_injective fixedInvolution).trans hfixedOrder
  have hfixedFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard factor hfactor
    fixedInvolution.val fixedInvolution.property hfixedAmbientOrder
  have hfixedCentralizer : fixedInvolution.val ∈ Subgroup.centralizer {imageInvolution.val} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have heq := congrArg Subtype.val hfixed
    change imageInvolution.val * fixedInvolution.val * imageInvolution.val⁻¹ = fixedInvolution.val at heq
    calc
      fixedInvolution.val * imageInvolution.val =
          (imageInvolution.val * fixedInvolution.val * imageInvolution.val⁻¹) * imageInvolution.val := by rw [heq]
      _ = imageInvolution.val * fixedInvolution.val := by group
  have hfixedImageNormalizer := image_centralizer_le component heven huniversal hquasisimple actor factor hfactor
    imageInvolution.val imageInvolution.property hinvolutionOrder hcard hfixedCentralizer
  have hfixedNormalizes := reverse_normalizes component hcontrol actor hactor factor hfactor
    fixedInvolution.val hfixedFusion hfixedImageNormalizer
  have hnotCentralizes : fixedInvolution.val ∉ Subgroup.centralizer (image : Set G) := by
    intro hcentral
    obtain ⟨_, other, hother, hcentralized⟩ := hfixedFusion
    exact hactor (BlockFusion.common_involution_forces_normalizer component heven huniversal hquasisimple
      factor other hfactor hother actor fixedInvolution.val hfixedAmbientOrder hcentral hcentralized)
  have hcommutator := QuasisimpleNormalizerCommutator.eq_factor image himageQuasi fixedInvolution.val
    hfixedNormalizes hnotCentralizes
  have hcommutatorLe : ⁅image, Subgroup.zpowers fixedInvolution.val⁆ ≤ factor := by
    apply Subgroup.commutator_le.mpr
    intro member hmember element helement
    have helementFactor : element ∈ factor := (Subgroup.zpowers_le.mpr fixedInvolution.property) helement
    have hconjugate : member * element * member⁻¹ ∈ factor :=
      (Subgroup.mem_normalizer_iff.mp (hfactorNormalizes hmember) element).mp helementFactor
    change member * element * member⁻¹ * element⁻¹ ∈ factor
    exact factor.mul_mem hconjugate (factor.inv_mem helementFactor)
  rw [hcommutator] at hcommutatorLe
  have hcardEq : Nat.card image = Nat.card factor :=
    Subgroup.card_map_of_injective (MulAut.conj actor).injective
  have heq : image = factor := Subgroup.eq_of_le_of_card_ge hcommutatorLe hcardEq.ge
  have hnormalizes := UniversalOrbitBlock.normalizes_of_anchor_image component heven huniversal hquasisimple
    factor hfactor actor (by change image ∈ UniversalOrbitBlock.block component; rwa [heq])
  exact hactor hnormalizes

theorem transporter_of_local_solvability {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component)) (hB : LocalB.LocalBProperty G)
    (hcore : ∀ element : G, orderOf element = 2 →
      Group.IsSolvable (componentClassificationOddCore (Subgroup.centralizer {element})))
    (houter : ∀ element : G, orderOf element = 2 →
      ∀ factor : Subgroup ((Subgroup.centralizer {element}) ⧸
        componentClassificationOddCore (Subgroup.centralizer {element})),
        IsComponentOf factor ⊤ → factor ≠ ⊤ →
          Group.IsSolvable (OuterAutomorphisms.Outer (factor ⧸ Subgroup.center factor)))
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (actor : G)
    (himageLe : UniversalOrbitBlock.conjugate factor actor ≤ UniversalOrbitBlock.normalizer component) :
    actor ∈ UniversalOrbitBlock.normalizer component :=
  transporter component heven huniversal hquasisimple hcard
    (external_control_of_local_solvability component heven huniversal hquasisimple hcard hB hcore houter)
    factor hfactor actor himageLe

end CFSG.ComponentClassification.BlockFactorContainment
