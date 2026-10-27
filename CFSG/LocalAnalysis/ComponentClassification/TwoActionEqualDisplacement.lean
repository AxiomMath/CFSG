module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionOddIntersection
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.TwoActionEqualDisplacement

theorem embedding {G : Type*} [Group G] (ambient acting intersection fixed : Subgroup G)
    (hfixed : fixed ≤ ambient) (hdisjoint : Disjoint ambient acting)
    (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hcentralizes : acting ≤ Subgroup.centralizer (fixed : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (actor : G) (hactor : actor ∈ ambient) (houtside : actor ∉ intersection)
    (hconjugate : acting.map (MulAut.conj actor).toMonoidHom ≤ fixed ⊔ acting) :
    ∃ homomorphism : acting →* fixed, Function.Injective homomorphism ∧
      ∀ member : acting, (homomorphism member).val = member.val⁻¹ * (actor * member.val * actor⁻¹) := by
  have hmem : ∀ member ∈ acting, member⁻¹ * (actor * member * actor⁻¹) ∈ fixed := by
    intro member hmember
    have hproduct : member⁻¹ * (actor * member * actor⁻¹) ∈ fixed ⊔ acting :=
      (fixed ⊔ acting).mul_mem ((fixed ⊔ acting).inv_mem ((le_sup_right : acting ≤ fixed ⊔ acting) hmember))
        (hconjugate (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩))
    have hambient : member⁻¹ * (actor * member * actor⁻¹) ∈ ambient := by
      have hconjugateMem := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (ambient : Set G)).inv_mem (hnormalizes hmember)) actor).mp hactor
      have hmem := ambient.mul_mem hconjugateMem (ambient.inv_mem hactor)
      convert hmem using 1
      group
    exact (NormalizedProduct.inf_eq fixed acting ambient
      (hcentralizes.trans (Subgroup.centralizer_le_normalizer _)) hfixed hdisjoint) ▸
        (show member⁻¹ * (actor * member * actor⁻¹) ∈ (fixed ⊔ acting) ⊓ ambient from ⟨hproduct, hambient⟩)
  let displacement : acting → fixed := fun member =>
    ⟨member.val⁻¹ * (actor * member.val * actor⁻¹), hmem member.val member.property⟩
  have hidentity : ∀ member : acting, actor * member.val * actor⁻¹ = member.val * (displacement member).val := by
    intro member
    change actor * member.val * actor⁻¹ = member.val * (member.val⁻¹ * (actor * member.val * actor⁻¹))
    group
  let homomorphism : acting →* fixed :=
    { toFun := displacement
      map_one' := by
        apply Subtype.ext
        change (1 : G)⁻¹ * (actor * 1 * actor⁻¹) = 1
        group
      map_mul' := by
        intro left right
        apply Subtype.ext
        change (left.val * right.val)⁻¹ * (actor * (left.val * right.val) * actor⁻¹) =
          (displacement left).val * (displacement right).val
        have hcommute := (Subgroup.mem_centralizer_iff.mp (hcentralizes right.property)
          (displacement left).val (displacement left).property).symm
        calc
          _ = right.val⁻¹ * left.val⁻¹ * ((actor * left.val * actor⁻¹) *
                (actor * right.val * actor⁻¹)) := by group
          _ = right.val⁻¹ * left.val⁻¹ * ((left.val * (displacement left).val) *
                (right.val * (displacement right).val)) := by rw [hidentity left, hidentity right]
          _ = (displacement left).val * (displacement right).val := by
            calc
              _ = right.val⁻¹ * ((displacement left).val * right.val) *
                    (displacement right).val := by group
              _ = right.val⁻¹ * (right.val * (displacement left).val) *
                    (displacement right).val := by rw [hcommute]
              _ = _ := by group }
  refine ⟨homomorphism, (MonoidHom.ker_eq_bot_iff homomorphism).mp ?_, fun member => rfl⟩
  apply le_antisymm _ bot_le
  intro member hmember
  apply Subgroup.mem_bot.mpr
  by_contra hne
  have hambientNe : member.val ≠ 1 := fun hone => hne (Subtype.ext hone)
  have hone : member.val⁻¹ * (actor * member.val * actor⁻¹) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hmember)
  have hcommutes : member.val * actor = actor * member.val :=
    (mul_inv_eq_iff_eq_mul.mp (inv_mul_eq_one.mp hone).symm).symm
  exact houtside (hcentralizers member.val member.property hambientNe
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcommutes.symm, hactor⟩)

theorem abelian_image {G : Type*} [Group G] [Finite G] (acting intersection fixed : Subgroup G)
    (htwo : IsPGroup 2 acting) (hcentralizes : acting ≤ Subgroup.centralizer (fixed : Set G))
    (hcommutator : ⁅acting, intersection⁆ ≤ (componentClassificationOddCore intersection).map intersection.subtype)
    (actor : G) (homomorphism : acting →* fixed) (hinjective : Function.Injective homomorphism)
    (hformula : ∀ member : acting, (homomorphism member).val = member.val⁻¹ * (actor * member.val * actor⁻¹))
    (himage : (fixed.subtype.comp homomorphism).range ≤ intersection.map (MulAut.conj actor).toMonoidHom) :
    IsMulCommutative acting := by
  let image := (fixed.subtype.comp homomorphism).range
  let conjugateActing := acting.map (MulAut.conj actor).toMonoidHom
  let conjugateCore := ((componentClassificationOddCore intersection).map intersection.subtype).map
    (MulAut.conj actor).toMonoidHom
  have himageFixed : image ≤ fixed := by
    rintro member ⟨preimage, rfl⟩
    exact (homomorphism preimage).property
  have hcommutatorImage : ⁅image, image⁆ ≤ ⁅conjugateActing, image⁆ := by
    apply Subgroup.commutator_le.mpr
    intro first hfirst second hsecond
    obtain ⟨preimage, heq⟩ := hfirst
    have hpreimage : actor * preimage.val * actor⁻¹ ∈ conjugateActing :=
      Subgroup.mem_map.mpr ⟨preimage.val, preimage.property, rfl⟩
    have hcommutes : Commute preimage.val second :=
      (Subgroup.mem_centralizer_iff.mp (hcentralizes preimage.property) second (himageFixed hsecond)).symm
    have hidentity : actor * preimage.val * actor⁻¹ = preimage.val * first := by
      change (homomorphism preimage).val = first at heq
      rw [← heq, hformula]
      group
    have hbound := Subgroup.commutator_mem_commutator hpreimage hsecond
    have hfirstCommutes : Commute preimage.val first :=
      (Subgroup.mem_centralizer_iff.mp (hcentralizes preimage.property) first (himageFixed ⟨preimage, heq⟩)).symm
    have hfirstCentral : first ∈ Subgroup.centralizer {preimage.val} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hfirstCommutes.symm.eq
    have hsecondCentral : second ∈ Subgroup.centralizer {preimage.val} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcommutes.symm.eq
    have hcommutatorCentral : ⁅first, second⁆ ∈ Subgroup.centralizer {preimage.val} :=
      Subgroup.commutator_le_self _
        (Subgroup.commutator_mem_commutator hfirstCentral hsecondCentral)
    have hcommutatorCommutes : Commute preimage.val ⁅first, second⁆ :=
      (Subgroup.mem_centralizer_singleton_iff.mp hcommutatorCentral).symm
    rw [hidentity, commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hcommutes, mul_one,
      hcommutatorCommutes.mul_inv_cancel] at hbound
    exact hbound
  have hcoreBound : ⁅conjugateActing, image⁆ ≤ conjugateCore := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom) hcommutator
    rw [Subgroup.map_commutator] at hmap
    exact (Subgroup.commutator_mono le_rfl himage).trans hmap
  have hodd : Odd (Nat.card conjugateCore) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective,
      Subgroup.card_map_of_injective intersection.subtype_injective]
    exact OddCore.odd_card intersection
  have himageTwo : IsPGroup 2 image := by
    change IsPGroup 2 (fixed.subtype.comp homomorphism).range
    rw [MonoidHom.range_eq_map]
    exact (htwo.to_subgroup ⊤).map (fixed.subtype.comp homomorphism)
  have hbot := TwoActionOddIntersection.two_in_odd_eq_bot ⁅image, image⁆ conjugateCore
    (himageTwo.to_le (Subgroup.commutator_le_self image)) hodd (hcommutatorImage.trans hcoreBound)
  have hcentralImage := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  apply isMulCommutative_iff.mpr
  intro first second
  have hcommute : (homomorphism first).val * (homomorphism second).val =
      (homomorphism second).val * (homomorphism first).val :=
    (Subgroup.mem_centralizer_iff.mp (hcentralImage ⟨second, rfl⟩) _ ⟨first, rfl⟩)
  have hproductEq : (homomorphism (first * second)).val = (homomorphism (second * first)).val := by
    rw [map_mul, map_mul]
    exact hcommute
  exact hinjective (Subtype.ext hproductEq)

theorem image_le_conjugate {G : Type*} [Group G] (ambient acting intersection fixed : Subgroup G)
    (hfixed : fixed ≤ ambient) (hcentralizes : acting ≤ Subgroup.centralizer (fixed : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (actor : G) (hactor : actor ∈ ambient) (homomorphism : acting →* fixed)
    (hformula : ∀ member : acting, (homomorphism member).val = member.val⁻¹ * (actor * member.val * actor⁻¹))
    (central : acting) (hcentral : central ∈ Subgroup.center acting) (hne : central ≠ 1) :
    (fixed.subtype.comp homomorphism).range ≤ intersection.map (MulAut.conj actor).toMonoidHom := by
  have hidentity : ∀ member : acting, actor * member.val * actor⁻¹ = member.val * (homomorphism member).val := by
    intro member
    rw [hformula]
    group
  have hcentralConjugate : acting ≤ Subgroup.centralizer {actor * central.val * actor⁻¹} := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcommutes : member * central.val = central.val * member :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral (⟨member, hmember⟩ : acting))
    have hfixedCommutes : member * (homomorphism central).val = (homomorphism central).val * member :=
      (Subgroup.mem_centralizer_iff.mp (hcentralizes hmember) _ (homomorphism central).property).symm
    rw [hidentity central]
    calc
      member * (central.val * (homomorphism central).val) =
          (member * central.val) * (homomorphism central).val := by group
      _ = (central.val * member) * (homomorphism central).val := by rw [hcommutes]
      _ = central.val * (member * (homomorphism central).val) := by group
      _ = central.val * ((homomorphism central).val * member) := by rw [hfixedCommutes]
      _ = _ := by group
  have hambientNe : central.val ≠ 1 := fun hone => hne (Subtype.ext hone)
  rintro member ⟨preimage, heq⟩
  change (homomorphism preimage).val = member at heq
  have hconjugateCommutes : actor * preimage.val * actor⁻¹ ∈
      Subgroup.centralizer {actor * central.val * actor⁻¹} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcommutes := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral preimage)
    change preimage.val * central.val = central.val * preimage.val at hcommutes
    have hconjugateEq := congrArg (fun value : G => actor * value * actor⁻¹) hcommutes
    convert hconjugateEq using 1 <;> group
  have hdisplacementCentral : member ∈ Subgroup.centralizer {actor * central.val * actor⁻¹} := by
    rw [← heq, hformula]
    exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem
      (hcentralConjugate preimage.property)) hconjugateCommutes
  have hmemberAmbient : member ∈ ambient := heq ▸ hfixed (homomorphism preimage).property
  have hpreimageAmbient : actor⁻¹ * member * actor ∈ ambient := by
    exact ambient.mul_mem (ambient.mul_mem (ambient.inv_mem hactor) hmemberAmbient) hactor
  have hpreimageCentral : actor⁻¹ * member * actor ∈ Subgroup.centralizer {central.val} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hequal := congrArg (fun value : G => actor⁻¹ * value * actor)
      (Subgroup.mem_centralizer_singleton_iff.mp hdisplacementCentral)
    convert hequal using 1 <;> group
  apply Subgroup.mem_map.mpr
  refine ⟨actor⁻¹ * member * actor,
    hcentralizers central.val central.property hambientNe ⟨hpreimageCentral, hpreimageAmbient⟩, ?_⟩
  change actor * (actor⁻¹ * member * actor) * actor⁻¹ = member
  group

theorem abelian_embedding {G : Type*} [Group G] [Finite G] (ambient acting intersection fixed : Subgroup G)
    (hfixed : fixed ≤ intersection) (hintersection : intersection ≤ ambient)
    (htwo : IsPGroup 2 acting) (hdisjoint : Disjoint ambient acting)
    (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hcentralizes : acting ≤ Subgroup.centralizer (fixed : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hcommutator : ⁅acting, intersection⁆ ≤ (componentClassificationOddCore intersection).map intersection.subtype)
    (actor : G) (hactor : actor ∈ ambient) (houtside : actor ∉ intersection)
    (hconjugate : acting.map (MulAut.conj actor).toMonoidHom ≤ fixed ⊔ acting) :
    IsMulCommutative acting ∧ ∃ homomorphism : acting →* intersection, Function.Injective homomorphism := by
  obtain ⟨homomorphism, hinjective, hformula⟩ := embedding ambient acting intersection fixed
    (hfixed.trans hintersection) hdisjoint hnormalizes hcentralizes hcentralizers actor hactor houtside hconjugate
  have hab : IsMulCommutative acting := by
    by_cases htrivial : Subsingleton acting
    · exact isMulCommutative_iff.mpr (fun first second => htrivial.elim _ _)
    · let : Nontrivial acting := not_subsingleton_iff_nontrivial.mp htrivial
      have hcenterNontrivial := htwo.center_nontrivial
      let : Nontrivial (Subgroup.center acting) := hcenterNontrivial
      obtain ⟨central, hne⟩ := exists_ne (1 : Subgroup.center acting)
      have hcentralNe : central.val ≠ 1 := fun hone => hne (Subtype.ext hone)
      exact abelian_image acting intersection fixed htwo hcentralizes hcommutator actor homomorphism hinjective hformula
        (image_le_conjugate ambient acting intersection fixed (hfixed.trans hintersection) hcentralizes hcentralizers
          actor hactor homomorphism hformula central.val central.property hcentralNe)
  exact ⟨hab, (Subgroup.inclusion hfixed).comp homomorphism,
    (Subgroup.inclusion_injective hfixed).comp hinjective⟩

end CFSG.ComponentClassification.TwoActionEqualDisplacement
