module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionEightCharacters
public import CFSG.CharacterTheory.TwoRankLowerBound.FocalFusion

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def quaternionEightLinearHom (label : Fin 3) : QuaternionGroup 2 →* ℂ :=
  if label = 0 then quaternionCosetSignHom 2
  else if label = 1 then quaternionEightOtherSignHom
  else (quaternionCosetSignHom 2) * quaternionEightOtherSignHom

@[expose] def quaternionEightFourRepresentative (label : Fin 3) : QuaternionGroup 2 :=
  if label = 0 then QuaternionGroup.a (1 : ZMod 4)
  else if label = 1 then QuaternionGroup.xa (0 : ZMod 4)
  else QuaternionGroup.xa (1 : ZMod 4)

set_option backward.isDefEq.respectTransparency false in
theorem quaternionEightLinearHom_representative (label member : Fin 3) :
    quaternionEightLinearHom label (quaternionEightFourRepresentative member) =
      if label = member then 1 else -1 := by
  fin_cases label <;> fin_cases member <;>
    norm_num [quaternionEightLinearHom, quaternionEightFourRepresentative,
      quaternionCosetSignHom, quaternionCosetSign, quaternionEightOtherSignHom,
      MonoidHom.mul_apply, quaternionEightParityChar, AddChar.add_apply, quarticAddChar,
      quarticValue, ZMod.val]

set_option backward.isDefEq.respectTransparency false in
theorem quaternionEight_element_class (element : QuaternionGroup 2) :
    element = 1 ∨ element = QuaternionGroup.a (2 : ZMod 4) ∨
      ∃ label : Fin 3, element = quaternionEightFourRepresentative label ∨
        element = (quaternionEightFourRepresentative label)⁻¹ := by
  cases element with
  | a residue =>
    fin_cases residue
    · left; rfl
    · right; right; exact ⟨0, Or.inl rfl⟩
    · right; left; rfl
    · right; right
      refine ⟨0, Or.inr ?_⟩
      change QuaternionGroup.a (n := 2) (3 : ZMod 4) = (QuaternionGroup.a (n := 2) (1 : ZMod 4))⁻¹
      rw [quaternion_a_inv]
      congr 1
  | xa residue =>
    right; right
    fin_cases residue
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨2, Or.inl rfl⟩
    · refine ⟨1, Or.inr ?_⟩
      change QuaternionGroup.xa (n := 2) (2 : ZMod 4) = (QuaternionGroup.xa (n := 2) (0 : ZMod 4))⁻¹
      rw [quaternion_xa_inv]
      congr 1
    · refine ⟨2, Or.inr ?_⟩
      change QuaternionGroup.xa (n := 2) (3 : ZMod 4) = (QuaternionGroup.xa (n := 2) (1 : ZMod 4))⁻¹
      rw [quaternion_xa_inv]
      congr 1

theorem quaternionEight_representative_order (label : Fin 3) :
    orderOf (quaternionEightFourRepresentative label) = 4 := by
  fin_cases label
  · exact QuaternionGroup.orderOf_a_one
  · exact QuaternionGroup.orderOf_xa _
  · exact QuaternionGroup.orderOf_xa _

theorem quaternionEight_involution_order : orderOf (QuaternionGroup.a (n := 2) (2 : ZMod 4)) = 2 := by
  have horder := quaternion_square_order (parameter := 2)
  rw [QuaternionGroup.a_one_pow] at horder
  exact horder

set_option backward.isDefEq.respectTransparency false in
theorem quaternionEight_representative_isConj_inverse (label : Fin 3) :
    IsConj (quaternionEightFourRepresentative label) (quaternionEightFourRepresentative label)⁻¹ := by
  apply isConj_iff.mpr
  fin_cases label
  · refine ⟨QuaternionGroup.xa (0 : ZMod 4), ?_⟩
    change QuaternionGroup.xa (n := 2) (0 : ZMod 4) * QuaternionGroup.a (n := 2) (1 : ZMod 4) *
      (QuaternionGroup.xa (n := 2) (0 : ZMod 4))⁻¹ = (QuaternionGroup.a (n := 2) (1 : ZMod 4))⁻¹
    rw [quaternion_xa_inv, quaternion_a_inv, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]
    congr 1
  · refine ⟨QuaternionGroup.a (1 : ZMod 4), ?_⟩
    change QuaternionGroup.a (n := 2) (1 : ZMod 4) * QuaternionGroup.xa (n := 2) (0 : ZMod 4) *
      (QuaternionGroup.a (n := 2) (1 : ZMod 4))⁻¹ = (QuaternionGroup.xa (n := 2) (0 : ZMod 4))⁻¹
    rw [quaternion_a_inv, quaternion_xa_inv, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
    congr 1
  · refine ⟨QuaternionGroup.a (1 : ZMod 4), ?_⟩
    change QuaternionGroup.a (n := 2) (1 : ZMod 4) * QuaternionGroup.xa (n := 2) (1 : ZMod 4) *
      (QuaternionGroup.a (n := 2) (1 : ZMod 4))⁻¹ = (QuaternionGroup.xa (n := 2) (1 : ZMod 4))⁻¹
    rw [quaternion_a_inv, quaternion_xa_inv, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
    congr 1

theorem isConj_map_group_hom {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) {left right : source} (hconjugate : IsConj left right) :
    IsConj (homomorphism left) (homomorphism right) := by
  obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp hconjugate
  apply isConj_iff.mpr
  refine ⟨homomorphism conjugator, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hconjugator]

theorem equivalence_relation_three_not_universal_singleton
    (relation : Fin 3 → Fin 3 → Prop) (hreflexive : ∀ member, relation member member)
    (hsymmetric : ∀ {left right}, relation left right → relation right left)
    (htransitive : ∀ {first second third}, relation first second → relation second third → relation first third)
    (hnotall : ¬ ∀ left right, relation left right) :
    ∃ singleton : Fin 3, ∀ other, relation singleton other → other = singleton := by
  by_contra! hnone
  have hall : ∀ left right, relation left right := by
    intro left right
    by_contra hnot
    obtain ⟨leftOther, hleftOther, hleftNe⟩ := hnone left
    obtain ⟨rightOther, hrightOther, hrightNe⟩ := hnone right
    fin_cases left <;> fin_cases right <;> fin_cases leftOther <;> fin_cases rightOther <;>
      first
      | exact hnot (hreflexive _)
      | exact hnot hleftOther
      | exact hnot (hsymmetric hrightOther)
      | exact hnot (htransitive hleftOther (hsymmetric hrightOther))
      | exact hleftNe rfl
      | exact hrightNe rfl
  exact hnotall hall

theorem orderOf_eq_of_isConj {G : Type*} [Group G] {left right : G}
    (hconjugate : IsConj left right) : orderOf left = orderOf right := by
  obtain ⟨conjugator, rfl⟩ := isConj_iff.mp hconjugate
  exact ((MulAut.conj conjugator).orderOf_eq left).symm

set_option backward.isDefEq.respectTransparency false in
theorem quaternionEightLinearHom_involution (label : Fin 3) :
    quaternionEightLinearHom label (QuaternionGroup.a (2 : ZMod 4)) = 1 := by
  fin_cases label <;>
    norm_num [quaternionEightLinearHom, quaternionCosetSignHom, quaternionCosetSign,
      quaternionEightOtherSignHom, MonoidHom.mul_apply, quaternionEightParityChar_two]

theorem quaternionEight_embedded_character_class {G : Type*} [Group G]
    (embedding : QuaternionGroup 2 →* G) (hinjective : Function.Injective embedding)
    (label : Fin 3) (element : QuaternionGroup 2) :
    (orderOf (embedding element) = 1 ∧ quaternionEightLinearHom label element = 1) ∨
    (orderOf (embedding element) = 2 ∧ quaternionEightLinearHom label element = 1) ∨
    ∃ member : Fin 3, orderOf (embedding element) = 4 ∧
      IsConj (embedding (quaternionEightFourRepresentative member)) (embedding element) ∧
      quaternionEightLinearHom label element = if label = member then 1 else -1 := by
  rcases quaternionEight_element_class element with hequal | hequal | ⟨member, hequal | hequal⟩
  · subst element
    left
    simp only [map_one, orderOf_one, and_self]
  · subst element
    right; left
    exact ⟨(orderOf_injective embedding hinjective _).trans quaternionEight_involution_order,
      quaternionEightLinearHom_involution label⟩
  · subst element
    right; right
    exact ⟨member, (orderOf_injective embedding hinjective _).trans
      (quaternionEight_representative_order member), IsConj.refl _,
      quaternionEightLinearHom_representative label member⟩
  · subst element
    right; right
    refine ⟨member, ?_, isConj_map_group_hom embedding
      (quaternionEight_representative_isConj_inverse member), ?_⟩
    · rw [orderOf_injective embedding hinjective, orderOf_inv,
        quaternionEight_representative_order]
    · rw [map_inv, quaternionEightLinearHom_representative]
      split_ifs <;> norm_num

theorem quaternionEight_singleton_class_fusion_invariant {G : Type*} [Group G]
    (embedding : QuaternionGroup 2 →* G) (hinjective : Function.Injective embedding)
    (singleton : Fin 3)
    (hsingleton : ∀ member : Fin 3,
      IsConj (embedding (quaternionEightFourRepresentative singleton))
        (embedding (quaternionEightFourRepresentative member)) → member = singleton)
    (left right : QuaternionGroup 2) (hconjugate : IsConj (embedding left) (embedding right)) :
    quaternionEightLinearHom singleton left = quaternionEightLinearHom singleton right := by
  have horder := orderOf_eq_of_isConj hconjugate
  have hleft := quaternionEight_embedded_character_class embedding hinjective singleton left
  have hright := quaternionEight_embedded_character_class embedding hinjective singleton right
  rcases hleft with ⟨hleftOrder, hleftValue⟩ | ⟨hleftOrder, hleftValue⟩ |
    ⟨leftLabel, hleftOrder, hleftConjugate, hleftValue⟩
  · rcases hright with ⟨hrightOrder, hrightValue⟩ | ⟨hrightOrder, hrightValue⟩ |
      ⟨rightLabel, hrightOrder, hrightConjugate, hrightValue⟩
    · exact hleftValue.trans hrightValue.symm
    · omega
    · omega
  · rcases hright with ⟨hrightOrder, hrightValue⟩ | ⟨hrightOrder, hrightValue⟩ |
      ⟨rightLabel, hrightOrder, hrightConjugate, hrightValue⟩
    · omega
    · exact hleftValue.trans hrightValue.symm
    · omega
  · rcases hright with ⟨hrightOrder, hrightValue⟩ | ⟨hrightOrder, hrightValue⟩ |
      ⟨rightLabel, hrightOrder, hrightConjugate, hrightValue⟩
    · omega
    · omega
    · have hlabels := hleftConjugate.trans (hconjugate.trans hrightConjugate.symm)
      have hequal : singleton = leftLabel ↔ singleton = rightLabel := by
        constructor
        · intro hequal
          subst leftLabel
          exact (hsingleton rightLabel hlabels).symm
        · intro hequal
          subst rightLabel
          exact (hsingleton leftLabel hlabels.symm).symm
      rw [hleftValue, hrightValue]
      simp only [hequal]

theorem perfect_sylow_quaternion_eight_total_four_fusion {G : Type*}
    [Group G] [Finite G] [Group.IsPerfect G] (sylow : Sylow 2 G)
    (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    ∀ left right : (sylow : Subgroup G), orderOf left = 4 → orderOf right = 4 →
      IsConj (left : G) (right : G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let embedding : QuaternionGroup 2 →* G :=
    (sylow : Subgroup G).subtype.comp isomorphism.symm.toMonoidHom
  have hinjective : Function.Injective embedding :=
    (sylow : Subgroup G).subtype_injective.comp isomorphism.symm.injective
  let relation := fun left right : Fin 3 =>
    IsConj (embedding (quaternionEightFourRepresentative left))
      (embedding (quaternionEightFourRepresentative right))
  have hall : ∀ left right, relation left right := by
    by_contra hnotall
    obtain ⟨singleton, hsingleton⟩ := equivalence_relation_three_not_universal_singleton
      relation (fun _ => IsConj.refl _) (fun hconj => hconj.symm)
      (fun hfirst hsecond => hfirst.trans hsecond) hnotall
    let linearHom := (quaternionEightLinearHom singleton).comp isomorphism.toMonoidHom
    have htrivial := fusion_invariant_hom_trivial_of_perfect_sylow 2 sylow linearHom.toHomUnits
      (by
        intro left right conjugator hequal
        apply Units.ext
        simp only [MonoidHom.coe_toHomUnits, linearHom, MonoidHom.comp_apply]
        apply quaternionEight_singleton_class_fusion_invariant embedding hinjective singleton hsingleton
        apply isConj_iff.mpr
        refine ⟨conjugator, ?_⟩
        simpa only [embedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply, Subgroup.coe_subtype] using hequal)
    have hnontrivial : ∃ other : Fin 3, other ≠ singleton := by
      fin_cases singleton
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    obtain ⟨other, hne⟩ := hnontrivial
    have hvalue := congrArg (fun unit : ℂˣ => (unit : ℂ))
      (htrivial (isomorphism.symm (quaternionEightFourRepresentative other)))
    simp only [MonoidHom.coe_toHomUnits, linearHom, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      quaternionEightLinearHom_representative, ite_eq_right (Ne.symm hne), Units.val_one] at hvalue
    exact (by norm_num : (-1 : ℂ) ≠ 1) hvalue
  intro left right hleftOrder hrightOrder
  have hleftClass := quaternionEight_embedded_character_class embedding hinjective 0 (isomorphism left)
  have hrightClass := quaternionEight_embedded_character_class embedding hinjective 0 (isomorphism right)
  have hembeddedLeft : embedding (isomorphism left) = (left : G) := by
    simp only [embedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype]
  have hembeddedRight : embedding (isomorphism right) = (right : G) := by
    simp only [embedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype]
  have hleftAmbientOrder : orderOf (embedding (isomorphism left)) = 4 := by
    rw [hembeddedLeft, Subgroup.orderOf_coe, hleftOrder]
  have hrightAmbientOrder : orderOf (embedding (isomorphism right)) = 4 := by
    rw [hembeddedRight, Subgroup.orderOf_coe, hrightOrder]
  rcases hleftClass with ⟨hbad, _⟩ | ⟨hbad, _⟩ | ⟨leftLabel, _, hleftConjugate, _⟩
  · omega
  · omega
  · rcases hrightClass with ⟨hbad, _⟩ | ⟨hbad, _⟩ | ⟨rightLabel, _, hrightConjugate, _⟩
    · omega
    · omega
    · rw [← hembeddedLeft, ← hembeddedRight]
      exact hleftConjugate.symm.trans ((hall leftLabel rightLabel).trans hrightConjugate)

end CFSG.TwoRankLowerBound.Helpers
