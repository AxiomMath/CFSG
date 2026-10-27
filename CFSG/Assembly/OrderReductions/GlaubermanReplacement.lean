module

public import CFSG.Assembly.OrderReductions.ReplacementGrowth

public section

namespace CFSG.OrderReductions.GlaubermanReplacement

open CFSG.OrderReductions.ReplacementGeometry CFSG.OrderReductions.ReplacementGrowth CFSG.OrderReductions.ThompsonCenter

theorem replacement_avoids_normal {group : Type*} [Group group]
    (subgroup normal : Subgroup group) [normal.Normal]
    (element : normal) (outside : element.val ∉ normalizerProduct normal subgroup)
    (normalizes : element.val ∈ Subgroup.normalizer (normalizerProduct normal subgroup : Set group)) :
    ¬ normal ≤ replacement subgroup element.val := by
  have contains : subgroup ≤ normalizerProduct normal subgroup := le_sup_left
  have conjugate_le := conjugate_le_of_normalizes subgroup (normalizerProduct normal subgroup) contains normalizes
  have replacement_le := (replacement_le_product subgroup element.val).trans (sup_le contains conjugate_le)
  intro normal_le
  exact outside (replacement_le (normal_le element.property))

theorem exists_improved_maximum {group : Type*} [Group group] [Finite group]
    (subgroup normal : Subgroup group) [normal.Normal]
    (maximal : MaximumOrderAbelian group subgroup)
    (central : commutator normal ≤ Subgroup.center normal) (odd_order : Odd (Nat.card normal))
    (derived_le : ⁅normal, normal⁆ ≤ subgroup)
    (condition : NormalizerCondition ↥(subgroup ⊔ normal))
    (not_normalizes : ¬ normal ≤ Subgroup.normalizer (subgroup : Set group)) :
    ∃ improved : Subgroup group, MaximumOrderAbelian group improved ∧ ¬ normal ≤ improved ∧
      localNormalizer normal subgroup < localNormalizer normal improved := by
  obtain ⟨element, outside, normalizes⟩ :=
    exists_normalizing_element_outside normal subgroup condition not_normalizes
  have : IsMulCommutative subgroup := maximal.1
  have pair := conjugate_pair_mutually_normalizes subgroup (normalizerProduct normal subgroup)
    (show subgroup ≤ normalizerProduct normal subgroup from le_sup_left)
    (normalizerProduct_normalizes normal subgroup) normalizes
  exact ⟨replacement subgroup element.val,
    replacement_maximum_order_abelian subgroup normal maximal central odd_order derived_le element pair.1 pair.2,
    replacement_avoids_normal subgroup normal element outside normalizes,
    replacement_grows_normalizer subgroup normal derived_le element outside normalizes⟩

theorem replacement_theorem_of_normalizer_condition {group : Type*} [Group group] [Finite group]
    (normal : Subgroup group) [normal.Normal]
    (central : commutator normal ≤ Subgroup.center normal) (odd_order : Odd (Nat.card normal))
    (derived_le : ⁅normal, normal⁆ ≤ thompsonCenter group)
    (condition : ∀ subgroup : Subgroup group, NormalizerCondition ↥(subgroup ⊔ normal)) :
    (∀ subgroup : Subgroup group, MaximumOrderAbelian group subgroup → normal ≤ subgroup) ∨
      ∃ subgroup : Subgroup group, MaximumOrderAbelian group subgroup ∧ ¬ normal ≤ subgroup ∧
        normal ≤ Subgroup.normalizer (subgroup : Set group) := by
  classical
  by_cases all_contain : ∀ subgroup : Subgroup group, MaximumOrderAbelian group subgroup → normal ≤ subgroup
  · exact Or.inl all_contain
  · apply Or.inr
    let candidates : Set (Subgroup group) :=
      {subgroup | MaximumOrderAbelian group subgroup ∧ ¬ normal ≤ subgroup}
    have nonempty : candidates.Nonempty := by
      push Not at all_contain
      exact all_contain
    obtain ⟨subgroup, maximal⟩ := Set.Finite.exists_maximalFor
      (fun candidate : Subgroup group => localNormalizer normal candidate) candidates (Set.toFinite _) nonempty
    refine ⟨subgroup, maximal.prop.1, maximal.prop.2, ?_⟩
    by_contra not_normalizes
    have derived_subgroup := derived_le.trans (thompsonCenter_le_maximum_order_abelian subgroup maximal.prop.1)
    obtain ⟨improved, improved_maximal, improved_avoids, grows⟩ :=
      exists_improved_maximum subgroup normal maximal.prop.1 central odd_order derived_subgroup
        (condition subgroup) not_normalizes
    exact maximal.not_gt ⟨improved_maximal, improved_avoids⟩ grows

theorem glauberman_replacement {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime) (prime_group : IsPGroup prime group)
    (normal : Subgroup group) [normal.Normal]
    (central : commutator normal ≤ Subgroup.center normal)
    (derived_le : ⁅normal, normal⁆ ≤ thompsonCenter group) :
    (∀ subgroup : Subgroup group, MaximumOrderAbelian group subgroup → normal ≤ subgroup) ∨
      ∃ subgroup : Subgroup group, MaximumOrderAbelian group subgroup ∧ ¬ normal ≤ subgroup ∧
        normal ≤ Subgroup.normalizer (subgroup : Set group) := by
  obtain ⟨exponent, card_eq⟩ := (prime_group.to_subgroup normal).exists_card_eq
  have normal_odd : Odd (Nat.card normal) := card_eq ▸ odd_prime.pow
  apply replacement_theorem_of_normalizer_condition normal central normal_odd derived_le
  intro subgroup
  have : Group.IsNilpotent ↥(subgroup ⊔ normal) :=
    (prime_group.to_subgroup (subgroup ⊔ normal)).isNilpotent
  exact Group.normalizerCondition_of_isNilpotent

end CFSG.OrderReductions.GlaubermanReplacement
