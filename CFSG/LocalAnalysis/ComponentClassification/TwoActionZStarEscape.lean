module

public import CFSG.LocalAnalysis.ComponentClassification.SubgroupOddCoreNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoProductOddCore
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoActionZStarEscape

@[expose] def ZStar (G : Type*) [Group G] : Prop :=
  ∀ sylow : Sylow 2 G, ∀ element : G, orderOf element = 2 →
    element ∈ ((Subgroup.center (sylow : Subgroup G)).map (sylow : Subgroup G).subtype) →
    (∀ actor : G, actor * element * actor⁻¹ ∈ (sylow : Subgroup G) → actor * element * actor⁻¹ = element) →
    Subgroup.centralizer {element} ⊔ componentClassificationOddCore G = ⊤

theorem twoActionZStar {G : Type*} [Group G] [Finite G] : ZStar G := by
  intro S t ht hz hiso
  obtain ⟨z, hz, rfl⟩ := hz
  have hzo : orderOf z = 2 := by simpa using ht
  have hright : ∀ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) →
      g⁻¹ * (z : G) * g = z := by
    intro g hg
    simpa using hiso g⁻¹ (by simpa using hg)
  obtain ⟨hfac, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.glauberman_zStar_central_sylow_involution_univ
      S z hz hzo hright
  apply top_unique
  intro g _
  obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
  exact (Subgroup.centralizer ({(z : G)} : Set G) ⊔ componentClassificationOddCore G).mul_mem
    (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hk)

theorem escape {G : Type*} [Group G] [Finite G] (ambient acting intersection : Subgroup G)
    (hintersection : intersection ≤ ambient) (htwo : IsPGroup 2 acting)
    (hdisjoint : Disjoint ambient acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hproper : intersection ⊔ (componentClassificationOddCore ambient).map ambient.subtype ≠ ambient)
    (sylow : Sylow 2 ambient)
    (hcentralizes : acting ≤ Subgroup.centralizer
      ((((sylow : Subgroup ambient).map ambient.subtype : Subgroup G) : Set G)))
    (central : acting) (hcentral : central ∈ Subgroup.center acting) (horder : orderOf central = 2) :
    ∃ actor ∈ ambient,
      actor * central.val * actor⁻¹ ∈ (sylow : Subgroup ambient).map ambient.subtype ⊔ acting ∧
        actor * central.val * actor⁻¹ ≠ central.val := by
  classical
  let product := ambient ⊔ acting
  let fixed := (sylow : Subgroup ambient).map ambient.subtype
  let smaller := fixed ⊔ acting
  let core := (componentClassificationOddCore ambient).map ambient.subtype
  have hfixedAmbient : fixed ≤ ambient := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hfixedNormalizes : acting ≤ Subgroup.normalizer (fixed : Set G) :=
    hcentralizes.trans (Subgroup.centralizer_le_normalizer _)
  let productSylow := NormalizedProductSylow.sylow ambient acting htwo hnormalizesAmbient sylow hfixedNormalizes
  have hsmallerLe : smaller ≤ product := sup_le (hfixedAmbient.trans le_sup_left) le_sup_right
  have hproductSylow : (productSylow : Subgroup product) = smaller.subgroupOf product :=
    NormalizedProductSylow.coe_sylow ambient acting htwo hnormalizesAmbient sylow hfixedNormalizes
  have hcentralProduct : central.val ∈ product := (le_sup_right : acting ≤ product) central.property
  let localCentral : product := ⟨central.val, hcentralProduct⟩
  have hlocalOrder : orderOf localCentral = 2 :=
    ((orderOf_injective product.subtype product.subtype_injective localCentral).symm.trans
      (orderOf_injective acting.subtype acting.subtype_injective central)).trans horder
  have hambientNe : central.val ≠ 1 := by
    intro hone
    have heq : central = 1 := Subtype.ext hone
    rw [heq, orderOf_one] at horder
    omega
  have hactingCentral : acting ≤ Subgroup.centralizer {central.val} := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral (⟨member, hmember⟩ : acting))
  have hfixedCentral : fixed ≤ Subgroup.centralizer {central.val} := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact Subgroup.mem_centralizer_iff.mp (hcentralizes central.property) member hmember
  have hsmallCentral := sup_le hfixedCentral hactingCentral
  have hlocalCentral : localCentral ∈
      (Subgroup.center (productSylow : Subgroup product)).map (productSylow : Subgroup product).subtype := by
    have hmem : localCentral ∈ (productSylow : Subgroup product) := by
      rw [hproductSylow]
      exact (le_sup_right : acting ≤ smaller) central.property
    apply Subgroup.mem_map.mpr
    refine ⟨⟨localCentral, hmem⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro member
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsmallCentral (by
      have hmember := member.property
      simp only [hproductSylow] at hmember
      exact hmember))
  by_contra hnone
  have hlocalIsolated : ∀ actor : product,
      actor * localCentral * actor⁻¹ ∈ (productSylow : Subgroup product) →
        actor * localCentral * actor⁻¹ = localCentral := by
    intro actor hmem
    obtain ⟨left, hleft, right, hright, heq⟩ :=
      NormalizedProduct.coordinates ambient acting hnormalizesAmbient actor.val actor.property
    have hrightCommutes : Commute right central.val :=
      Subgroup.mem_centralizer_singleton_iff.mp (hactingCentral hright)
    have hconjugateEq : actor.val * central.val * actor.val⁻¹ = left * central.val * left⁻¹ := by
      rw [← heq]
      calc
        _ = left * (right * central.val * right⁻¹) * left⁻¹ := by group
        _ = _ := by rw [hrightCommutes.mul_inv_cancel]
    have hsmallMem : left * central.val * left⁻¹ ∈ smaller := by
      rw [hproductSylow] at hmem
      change actor.val * central.val * actor.val⁻¹ ∈ smaller at hmem
      rwa [hconjugateEq] at hmem
    have hleftFixed : left * central.val * left⁻¹ = central.val := by
      by_contra hchanged
      exact hnone ⟨left, hleft, hsmallMem, hchanged⟩
    exact Subtype.ext (hconjugateEq.trans hleftFixed)
  have hcover := (twoActionZStar (G := ↥(ambient ⊔ acting)))
    productSylow localCentral hlocalOrder hlocalCentral hlocalIsolated
  have hcoverMap := congrArg (Subgroup.map product.subtype) hcover
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    TwoProductOddCore.image_eq ambient acting hnormalizesAmbient htwo] at hcoverMap
  have hcentralizerLe : (Subgroup.centralizer {localCentral}).map product.subtype ≤ intersection ⊔ acting := by
    rintro member ⟨lift, hlift, rfl⟩
    apply NormalizedProductCentralizer.centralizer_le ambient acting intersection hnormalizesAmbient central.val
      hactingCentral (hcentralizers central.val central.property hambientNe)
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, lift.property⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hlift)
  have hbound : product ≤ (intersection ⊔ core) ⊔ acting := by
    rw [← hcoverMap]
    apply sup_le
    · exact hcentralizerLe.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · exact le_sup_right.trans le_sup_left
  have hcoreAmbient : core ≤ ambient := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hcoreNormalizes : acting ≤ Subgroup.normalizer (core : Set G) :=
    hnormalizesAmbient.trans (SubgroupOddCoreNormalizer.core ambient)
  have hjoinNormalizes : acting ≤ Subgroup.normalizer ((intersection ⊔ core : Subgroup G) : Set G) :=
    (le_inf hnormalizesIntersection hcoreNormalizes).trans
      (Subgroup.inf_normalizer_le_normalizer_sup intersection core)
  have hambientBound : ambient ≤ intersection ⊔ core := by
    rw [← NormalizedProduct.inf_eq (intersection ⊔ core) acting ambient hjoinNormalizes
      (sup_le hintersection hcoreAmbient) hdisjoint]
    exact le_inf (le_sup_left.trans hbound) le_rfl
  exact hproper (le_antisymm (sup_le hintersection hcoreAmbient) hambientBound)

end CFSG.ComponentClassification.TwoActionZStarEscape
