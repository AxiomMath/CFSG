module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionOddIntersection
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoSubgroupSylowConjugacy

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.TwoActionFusionEscape

theorem escape {G : Type*} [Group G] [Finite G] (ambient acting intersection : Subgroup G)
    (hintersection : intersection ≤ ambient) (htwo : IsPGroup 2 acting)
    (hdisjoint : Disjoint ambient acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hcommutator : ⁅acting, intersection⁆ ≤
      (componentClassificationOddCore intersection).map intersection.subtype)
    (sylow : Sylow 2 intersection)
    (hcentralizes : acting ≤ Subgroup.centralizer
      ((((sylow : Subgroup intersection).map intersection.subtype : Subgroup G) : Set G)))
    (central : acting) (hcentral : central ∈ Subgroup.center acting) (hne : central ≠ 1)
    (actor : G) (hactor : actor ∈ ambient)
    (hfused : actor * central.val * actor⁻¹ ∈ (sylow : Subgroup intersection).map intersection.subtype ⊔ acting)
    (hchanged : actor * central.val * actor⁻¹ ≠ central.val) :
    ∃ transporter ∈ ambient, transporter ∉ intersection ∧
      acting.map (MulAut.conj transporter).toMonoidHom ≤
        (sylow : Subgroup intersection).map intersection.subtype ⊔ acting := by
  let fixed := (sylow : Subgroup intersection).map intersection.subtype
  let smaller := fixed ⊔ acting
  have hfixedIntersection : fixed ≤ intersection := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hfixedAmbient := hfixedIntersection.trans hintersection
  have hfixedNormalizes : acting ≤ Subgroup.normalizer (fixed : Set G) :=
    hcentralizes.trans (Subgroup.centralizer_le_normalizer _)
  let displacement := central.val⁻¹ * (actor * central.val * actor⁻¹)
  have hdisplacementFixed : displacement ∈ fixed := by
    have hsmall : displacement ∈ smaller := smaller.mul_mem
      (smaller.inv_mem ((le_sup_right : acting ≤ smaller) central.property)) hfused
    have hconjugate := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (ambient : Set G)).inv_mem (hnormalizesAmbient central.property)) actor).mp hactor
    have hambient : displacement ∈ ambient := by
      convert ambient.mul_mem hconjugate (ambient.inv_mem hactor) using 1
      dsimp [displacement]
      group
    exact (NormalizedProduct.inf_eq fixed acting ambient hfixedNormalizes hfixedAmbient hdisjoint) ▸
      (show displacement ∈ smaller ⊓ ambient from ⟨hsmall, hambient⟩)
  have houtside : actor ∉ intersection := by
    intro hmem
    have hcore : displacement ∈ (componentClassificationOddCore intersection).map intersection.subtype := by
      have hmem := hcommutator (Subgroup.commutator_mem_commutator
        (acting.inv_mem central.property) hmem)
      change central.val⁻¹ * (actor * central.val * actor⁻¹) ∈ _
      simpa only [commutatorElement_def, inv_inv, mul_assoc] using hmem
    have hcoreOdd : Odd (Nat.card ((componentClassificationOddCore intersection).map intersection.subtype)) := by
      rw [Subgroup.card_map_of_injective intersection.subtype_injective]
      exact OddCore.odd_card intersection
    have hcyclicTwo : IsPGroup 2 (Subgroup.zpowers displacement) :=
      (sylow.isPGroup'.map intersection.subtype).to_le (Subgroup.zpowers_le.mpr hdisplacementFixed)
    have hbot := TwoActionOddIntersection.two_in_odd_eq_bot (Subgroup.zpowers displacement)
      ((componentClassificationOddCore intersection).map intersection.subtype) hcyclicTwo hcoreOdd
        (Subgroup.zpowers_le.mpr hcore)
    have hone : displacement = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers displacement)
    change central.val⁻¹ * (actor * central.val * actor⁻¹) = 1 at hone
    exact hchanged (inv_mul_eq_one.mp hone).symm
  have hambientNe : central.val ≠ 1 := fun hone => hne (Subtype.ext hone)
  have hactingCentral : acting ≤ Subgroup.centralizer {central.val} := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral (⟨member, hmember⟩ : acting))
  have hactingFusedCentral : acting ≤ Subgroup.centralizer {actor * central.val * actor⁻¹} := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcentralCommutes : Commute member central.val :=
      Subgroup.mem_centralizer_singleton_iff.mp (hactingCentral hmember)
    have hfixedCommutes : Commute member displacement :=
      (Subgroup.mem_centralizer_iff.mp (hcentralizes hmember) displacement hdisplacementFixed).symm
    have hidentity : actor * central.val * actor⁻¹ = central.val * displacement := by
      dsimp [displacement]
      group
    rw [hidentity]
    exact (hcentralCommutes.mul_right hfixedCommutes).eq
  have hinverseContained : acting.map (MulAut.conj actor⁻¹).toMonoidHom ≤ intersection ⊔ acting := by
    rintro member ⟨original, horiginal, rfl⟩
    apply NormalizedProductCentralizer.centralizer_le ambient acting intersection hnormalizesAmbient central.val
      hactingCentral (hcentralizers central.val central.property hambientNe)
    have hcentralMem : actor⁻¹ * original * actor ∈ Subgroup.centralizer {central.val} := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have heq := congrArg (fun value : G => actor⁻¹ * value * actor)
        (Subgroup.mem_centralizer_singleton_iff.mp (hactingFusedCentral horiginal))
      convert heq using 1 <;> group
    refine ⟨?_, ?_⟩
    · convert hcentralMem using 1
      change actor⁻¹ * original * actor⁻¹⁻¹ ∈ Subgroup.centralizer {central.val} ↔ _
      rw [inv_inv]
    ·
      convert (ambient ⊔ acting).mul_mem
        ((ambient ⊔ acting).mul_mem ((ambient ⊔ acting).inv_mem ((le_sup_left : ambient ≤ ambient ⊔ acting) hactor))
          ((le_sup_right : acting ≤ ambient ⊔ acting) horiginal))
        ((le_sup_left : ambient ≤ ambient ⊔ acting) hactor) using 1
      change actor⁻¹ * original * actor⁻¹⁻¹ ∈ ambient ⊔ acting ↔ _
      rw [inv_inv]
  let productSylow := NormalizedProductSylow.sylow intersection acting htwo hnormalizesIntersection sylow hfixedNormalizes
  obtain ⟨adjustment, hadjustment, hinto⟩ := TwoSubgroupSylowConjugacy.into (intersection ⊔ acting)
    (acting.map (MulAut.conj actor⁻¹).toMonoidHom) (htwo.map (MulAut.conj actor⁻¹).toMonoidHom)
      hinverseContained productSylow
  have hproductSylowImage : (productSylow : Subgroup ↥(intersection ⊔ acting)).map (intersection ⊔ acting).subtype =
      smaller := by
    rw [NormalizedProductSylow.coe_sylow, Subgroup.map_subgroupOf_eq_of_le
      (sup_le (hfixedIntersection.trans le_sup_left) le_sup_right)]
  rw [hproductSylowImage] at hinto
  obtain ⟨left, hleft, right, hright, heq⟩ := NormalizedProduct.coordinates intersection acting
    hnormalizesIntersection adjustment hadjustment
  let transporter := right⁻¹ * adjustment * actor⁻¹
  have hrightNormalizer : right ∈ Subgroup.normalizer (smaller : Set G) :=
    Subgroup.le_normalizer ((le_sup_right : acting ≤ smaller) hright)
  have hnormalizedLeft : right⁻¹ * adjustment ∈ intersection := by
    have hconjugate := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (intersection : Set G)).inv_mem (hnormalizesIntersection hright)) left).mp hleft
    rw [← heq]
    convert hconjugate using 1
    group
  have htransporterAmbient : transporter ∈ ambient :=
    ambient.mul_mem (hintersection hnormalizedLeft) (ambient.inv_mem hactor)
  have htransporterOutside : transporter ∉ intersection := by
    intro hmem
    have hinverse : actor⁻¹ ∈ intersection := by
      have hproduct := intersection.mul_mem (intersection.inv_mem hnormalizedLeft) hmem
      convert hproduct using 1
      dsimp [transporter]
      group
    exact houtside (intersection.inv_mem_iff.mp hinverse)
  refine ⟨transporter, htransporterAmbient, htransporterOutside, ?_⟩
  rintro member ⟨original, horiginal, rfl⟩
  have hinside := hinto (Subgroup.mem_map.mpr
    ⟨(MulAut.conj actor⁻¹) original, Subgroup.mem_map.mpr ⟨original, horiginal, rfl⟩, rfl⟩)
  have hconjugate := (Subgroup.mem_normalizer_iff.mp
    ((Subgroup.normalizer (smaller : Set G)).inv_mem hrightNormalizer) _).mp hinside
  convert hconjugate using 1
  simp only [MulAut.conj_apply, inv_inv]
  dsimp [transporter]
  group

end CFSG.ComponentClassification.TwoActionFusionEscape
