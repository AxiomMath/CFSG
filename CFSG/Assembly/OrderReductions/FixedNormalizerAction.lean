module

public import CFSG.Assembly.OrderReductions.FixedPairSylow
public import CFSG.Assembly.OrderReductions.PrimePart

public section

namespace CFSG.OrderReductions.FixedNormalizerAction

open CFSG.OrderReductions.FixedPairSylow

@[expose, instance_reducible] def fixedPointAction {group points : Type*} [Group group]
    [MulAction group points] (subgroup : Subgroup group) :
    MulAction (Subgroup.normalizer (subgroup : Set group)) (MulAction.fixedPoints subgroup points) where
  smul acting fixed := ⟨acting.val • fixed.val,
    normalizer_preserves_fixedPoints subgroup acting.val acting.property fixed.property⟩
  one_smul fixed := Subtype.ext (one_smul group fixed.val)
  mul_smul first second fixed := Subtype.ext (mul_smul first.val second.val fixed.val)

theorem pair_stabilizer_map {group points : Type*} [Group group] [MulAction group points]
    (first second : points) (acting : group) :
    (MulAction.stabilizer group first ⊓ MulAction.stabilizer group second).map
      (MulAut.conj acting).toMonoidHom =
        MulAction.stabilizer group (acting • first) ⊓ MulAction.stabilizer group (acting • second) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj acting).injective,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]

theorem pair_stabilizer_card_eq {group points : Type*} [Group group] [MulAction group points]
    (two_transitive : MulAction.IsMultiplyPretransitive group points 2)
    (first second third fourth : points) (first_distinct : first ≠ second) (third_distinct : third ≠ fourth) :
    Nat.card ↥(MulAction.stabilizer group first ⊓ MulAction.stabilizer group second) =
      Nat.card ↥(MulAction.stabilizer group third ⊓ MulAction.stabilizer group fourth) := by
  obtain ⟨acting, first_moves, second_moves⟩ :=
    MulAction.is_two_pretransitive_iff.mp two_transitive first_distinct third_distinct
  have mapped := pair_stabilizer_map first second acting
  rw [first_moves, second_moves] at mapped
  rw [← mapped, Subgroup.card_map_of_injective (MulAut.conj acting).injective]

theorem exists_normalizer_pair_transport {group points : Type*} [Group group] [Finite group]
    [MulAction group points] (prime : ℕ) [Fact (Nat.Prime prime)]
    (two_transitive : MulAction.IsMultiplyPretransitive group points 2)
    (subgroup : Subgroup group) (first second third fourth : points)
    (first_distinct : first ≠ second) (third_distinct : third ≠ fourth)
    (first_sylow : Sylow prime ↥(MulAction.stabilizer group first ⊓ MulAction.stabilizer group second))
    (first_image : (first_sylow : Subgroup
      ↥(MulAction.stabilizer group first ⊓ MulAction.stabilizer group second)).map
        (MulAction.stabilizer group first ⊓ MulAction.stabilizer group second).subtype = subgroup)
    (target_contains : subgroup ≤ MulAction.stabilizer group third ⊓ MulAction.stabilizer group fourth) :
    ∃ acting : Subgroup.normalizer (subgroup : Set group),
      acting.val • first = third ∧ acting.val • second = fourth := by
  classical
  let source_pair := MulAction.stabilizer group first ⊓ MulAction.stabilizer group second
  let target_pair := MulAction.stabilizer group third ⊓ MulAction.stabilizer group fourth
  obtain ⟨acting, first_moves, second_moves⟩ :=
    MulAction.is_two_pretransitive_iff.mp two_transitive first_distinct third_distinct
  have pair_image : source_pair.map (MulAut.conj acting).toMonoidHom = target_pair := by
    rw [pair_stabilizer_map, first_moves, second_moves]
  have original_card : Nat.card subgroup = CFSG.OrderReductions.PrimePart.primePart prime (Nat.card target_pair) := by
    rw [← first_image, CFSG.OrderReductions.PrimePart.sylow_map_card_eq_primePart,
      pair_stabilizer_card_eq two_transitive first second third fourth first_distinct third_distinct]
  have conjugate_contains : subgroup.map (MulAut.conj acting).toMonoidHom ≤ target_pair := by
    rw [← pair_image]
    exact Subgroup.map_mono (first_image ▸ Subgroup.map_subtype_le (first_sylow : Subgroup source_pair))
  have conjugate_card : Nat.card (subgroup.map (MulAut.conj acting).toMonoidHom) =
      CFSG.OrderReductions.PrimePart.primePart prime (Nat.card target_pair) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj acting).injective]
    exact original_card
  obtain ⟨target_sylow, target_image⟩ := CFSG.OrderReductions.PrimePart.exists_sylow_image_of_card
    prime subgroup target_pair target_contains original_card
  obtain ⟨conjugate_sylow, conjugate_image⟩ := CFSG.OrderReductions.PrimePart.exists_sylow_image_of_card
    prime (subgroup.map (MulAut.conj acting).toMonoidHom) target_pair conjugate_contains conjugate_card
  obtain ⟨adjustment, conjugates⟩ := MulAction.exists_smul_eq target_pair conjugate_sylow target_sylow
  have adjustment_image := sylow_subtype_smul_image prime target_pair conjugate_sylow adjustment
  rw [conjugates, target_image, conjugate_image] at adjustment_image
  have product_invariant : subgroup.map (MulAut.conj (adjustment.val * acting)).toMonoidHom = subgroup := by
    have composite : (MulAut.conj (adjustment.val * acting)).toMonoidHom =
        (MulAut.conj adjustment.val).toMonoidHom.comp (MulAut.conj acting).toMonoidHom := by
      ext element
      change (adjustment.val * acting) * element * (adjustment.val * acting)⁻¹ =
        adjustment.val * (acting * element * acting⁻¹) * adjustment.val⁻¹
      group
    rw [composite, ← Subgroup.map_map]
    exact adjustment_image.symm
  refine ⟨⟨adjustment.val * acting, Subgroup.mem_normalizer_iff_map_conj_eq.mpr product_invariant⟩, ?_, ?_⟩
  · rw [mul_smul, first_moves]
    exact adjustment.property.1
  · rw [mul_smul, second_moves]
    exact adjustment.property.2

theorem sylow_pair_normalizer_two_transitive {group points : Type*} [Group group] [Finite group]
    [MulAction group points] (prime : ℕ) [Fact (Nat.Prime prime)]
    (two_transitive : MulAction.IsMultiplyPretransitive group points 2)
    (first second : points) (distinct : first ≠ second)
    (sylow : Sylow prime ↥(MulAction.stabilizer group first ⊓ MulAction.stabilizer group second)) :
    let image := (sylow : Subgroup
      ↥(MulAction.stabilizer group first ⊓ MulAction.stabilizer group second)).map
        (MulAction.stabilizer group first ⊓ MulAction.stabilizer group second).subtype
    let _ := fixedPointAction (points := points) image
    MulAction.IsMultiplyPretransitive (Subgroup.normalizer (image : Set group))
      (MulAction.fixedPoints image points) 2 := by
  classical
  dsimp only
  let image := (sylow : Subgroup
    ↥(MulAction.stabilizer group first ⊓ MulAction.stabilizer group second)).map
      (MulAction.stabilizer group first ⊓ MulAction.stabilizer group second).subtype
  let := fixedPointAction (points := points) image
  have image_card := CFSG.OrderReductions.PrimePart.sylow_map_card_eq_primePart prime _ sylow
  have sylow_at_pair (third fourth : MulAction.fixedPoints image points) (other_distinct : third ≠ fourth) :
      ∃ internal : Sylow prime
          ↥(MulAction.stabilizer group third.val ⊓ MulAction.stabilizer group fourth.val),
        (internal : Subgroup
          ↥(MulAction.stabilizer group third.val ⊓ MulAction.stabilizer group fourth.val)).map
            (MulAction.stabilizer group third.val ⊓ MulAction.stabilizer group fourth.val).subtype = image := by
    apply CFSG.OrderReductions.PrimePart.exists_sylow_image_of_card
    · intro element element_mem
      exact ⟨MulAction.mem_fixedPoints.mp third.property ⟨element, element_mem⟩,
        MulAction.mem_fixedPoints.mp fourth.property ⟨element, element_mem⟩⟩
    · rw [← pair_stabilizer_card_eq two_transitive first second third.val fourth.val distinct
        (fun equal => other_distinct (Subtype.ext equal))]
      exact image_card
  apply MulAction.is_two_pretransitive_iff.mpr
  intro third fourth fifth sixth source_distinct target_distinct
  obtain ⟨internal, internal_image⟩ := sylow_at_pair third fourth source_distinct
  obtain ⟨acting, third_moves, fourth_moves⟩ := exists_normalizer_pair_transport prime two_transitive
    image third.val fourth.val fifth.val sixth.val
    (fun equal => source_distinct (Subtype.ext equal)) (fun equal => target_distinct (Subtype.ext equal))
    internal internal_image (by
      intro element element_mem
      exact ⟨MulAction.mem_fixedPoints.mp fifth.property ⟨element, element_mem⟩,
        MulAction.mem_fixedPoints.mp sixth.property ⟨element, element_mem⟩⟩)
  exact ⟨acting, Subtype.ext third_moves, Subtype.ext fourth_moves⟩

theorem mem_restricted_fixedPoints_iff {group points : Type*} [Group group]
    [MulAction group points] (subgroup larger : Subgroup group)
    (contains : larger ≤ Subgroup.normalizer (subgroup : Set group))
    (fixed : MulAction.fixedPoints subgroup points) :
    let _ := fixedPointAction (points := points) subgroup
    fixed ∈ MulAction.fixedPoints (larger.subgroupOf (Subgroup.normalizer (subgroup : Set group)))
      (MulAction.fixedPoints subgroup points) ↔ fixed.val ∈ MulAction.fixedPoints larger points := by
  let := fixedPointAction (points := points) subgroup
  constructor
  · intro internal_fixed
    apply MulAction.mem_fixedPoints.mpr
    intro acting
    let internal : larger.subgroupOf (Subgroup.normalizer (subgroup : Set group)) :=
      ⟨⟨acting.val, contains acting.property⟩, acting.property⟩
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp internal_fixed internal)
  · intro ambient_fixed
    apply MulAction.mem_fixedPoints.mpr
    intro acting
    exact Subtype.ext (MulAction.mem_fixedPoints.mp ambient_fixed ⟨acting.val.val, acting.property⟩)

end CFSG.OrderReductions.FixedNormalizerAction
