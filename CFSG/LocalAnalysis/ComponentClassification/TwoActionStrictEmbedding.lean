module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionDisplacementEmbedding
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionSylowChoices

public section

namespace CFSG.ComponentClassification.TwoActionStrictEmbedding

theorem escape {G : Type*} [Group G] [Finite G] (ambient acting intersection fixed sylow : Subgroup G)
    (hfixed : fixed ≤ sylow) (hsylow : sylow ≤ ambient) (hsylowTwo : IsPGroup 2 sylow)
    (hactingTwo : IsPGroup 2 acting) (hdisjoint : Disjoint ambient acting)
    (hcentralizes : acting ≤ Subgroup.centralizer (fixed : Set G))
    (hnormalizes : acting ≤ Subgroup.normalizer (sylow : Set G))
    (hintersection : intersection ⊓ sylow = fixed) (hlt : fixed < sylow) :
    ∃ actor ∈ sylow, actor ∉ intersection ∧
      actor ∈ Subgroup.normalizer ((fixed ⊔ acting : Subgroup G) : Set G) := by
  classical
  let product := sylow ⊔ acting
  let smaller := fixed ⊔ acting
  have hsmallerLe : smaller ≤ product := sup_le (hfixed.trans le_sup_left) le_sup_right
  have hfixedNormalizes : acting ≤ Subgroup.normalizer (fixed : Set G) :=
    hcentralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hsmallerAmbient : smaller ⊓ ambient = fixed :=
    NormalizedProduct.inf_eq fixed acting ambient hfixedNormalizes (hfixed.trans hsylow) hdisjoint
  have hproper : smaller < product := by
    apply lt_of_le_of_ne hsmallerLe
    intro heq
    have hle : sylow ≤ fixed := by
      rw [← hsmallerAmbient]
      exact le_inf (by rw [heq]; exact le_sup_left) hsylow
    exact (not_le_of_gt hlt) hle
  have hproductTwo : IsPGroup 2 product := hsylowTwo.to_sup_of_normal_left' hactingTwo hnormalizes
  let : Group.IsNilpotent product := hproductTwo.isNilpotent
  let localSmaller := smaller.subgroupOf product
  have hlocalProper : localSmaller ≠ ⊤ := by
    intro heq
    have hle : product ≤ smaller := by
      intro member hmember
      have hmem : (⟨member, hmember⟩ : product) ∈ localSmaller := by rw [heq]; exact Subgroup.mem_top _
      exact hmem
    exact (not_le_of_gt hproper) hle
  have hnotSelf : Subgroup.normalizer (localSmaller : Set product) ≠ localSmaller := by
    intro heq
    exact hlocalProper ((normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent) localSmaller heq)
  have hnotLe : ¬ Subgroup.normalizer (localSmaller : Set product) ≤ localSmaller := by
    intro hle
    exact hnotSelf (le_antisymm hle Subgroup.le_normalizer)
  obtain ⟨member, hmember, houtside⟩ := IsConcreteLE.not_le_iff_exists.mp hnotLe
  have hambientNormalizer : member.val ∈ Subgroup.normalizer (smaller : Set G) := by
    have hnormalizerEq := Subgroup.subgroupOf_normalizer_eq hsmallerLe
    rw [← hnormalizerEq] at hmember
    exact hmember
  obtain ⟨left, hleft, right, hright, heq⟩ := NormalizedProduct.coordinates sylow acting hnormalizes
    member.val member.property
  have hrightNormalizes : right ∈ Subgroup.normalizer (smaller : Set G) :=
    Subgroup.le_normalizer ((le_sup_right : acting ≤ smaller) hright)
  have hleftNormalizes : left ∈ Subgroup.normalizer (smaller : Set G) := by
    have hmem := (Subgroup.normalizer (smaller : Set G)).mul_mem hambientNormalizer
      ((Subgroup.normalizer _).inv_mem hrightNormalizes)
    rw [← heq, mul_inv_cancel_right] at hmem
    exact hmem
  have hleftNotFixed : left ∉ fixed := by
    intro hfixedMem
    apply houtside
    change member.val ∈ smaller
    rw [← heq]
    exact Subgroup.mul_mem_sup hfixedMem hright
  refine ⟨left, hleft, ?_, hleftNormalizes⟩
  intro hleftIntersection
  exact hleftNotFixed (hintersection ▸
    (show left ∈ intersection ⊓ sylow from ⟨hleftIntersection, hleft⟩))

theorem embedding {G : Type*} [Group G] [Finite G] (ambient acting intersection : Subgroup G)
    (hintersection : intersection ≤ ambient) (htwo : IsPGroup 2 acting)
    (hdisjoint : Disjoint ambient acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hcommutator : ⁅acting, intersection⁆ ≤
      (CFSG.Open.componentClassificationOddCore intersection).map intersection.subtype)
    (hstrict : ∀ first : Sylow 2 intersection, ∀ second : Sylow 2 ambient,
      Nat.card (first : Subgroup intersection) < Nat.card (second : Subgroup ambient)) :
    ∃ first : Sylow 2 intersection,
      ∃ homomorphism : acting →* Subgroup.center ((first : Subgroup intersection).map intersection.subtype),
        Function.Injective homomorphism := by
  obtain ⟨first, second, hle, heq, hnormalizes, hcentral⟩ := TwoActionSylowChoices.choices ambient acting intersection
    hintersection htwo hnormalizesAmbient hnormalizesIntersection hcommutator
  let firstImage := (first : Subgroup intersection).map intersection.subtype
  let secondImage := (second : Subgroup ambient).map ambient.subtype
  have hfirstCard : Nat.card firstImage = Nat.card (first : Subgroup intersection) :=
    Subgroup.card_map_of_injective intersection.subtype_injective
  have hsecondCard : Nat.card secondImage = Nat.card (second : Subgroup ambient) :=
    Subgroup.card_map_of_injective ambient.subtype_injective
  have hlt : firstImage < secondImage := by
    apply lt_of_le_of_ne hle
    intro hequal
    have hcards := congrArg (fun subgroup : Subgroup G => Nat.card subgroup) hequal
    rw [hfirstCard, hsecondCard] at hcards
    exact (Nat.ne_of_lt (hstrict first second)) hcards
  have hsecondAmbient : secondImage ≤ ambient := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hcentralizes : acting ≤ Subgroup.centralizer (firstImage : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral
  obtain ⟨actor, hactor, houtside, hproductNormalizes⟩ := escape ambient acting intersection firstImage secondImage
    hle hsecondAmbient (second.isPGroup'.map ambient.subtype) htwo hdisjoint hcentralizes hnormalizes heq hlt
  obtain ⟨homomorphism, hinjective⟩ := TwoActionDisplacementEmbedding.embedding ambient acting intersection firstImage
    (hle.trans hsecondAmbient) hdisjoint hnormalizesAmbient hcentralizes hcentralizers actor
    (hsecondAmbient hactor) houtside hproductNormalizes
  exact ⟨first, homomorphism, hinjective⟩

end CFSG.ComponentClassification.TwoActionStrictEmbedding
