module

public import CFSG.Assembly.OrderReductions.InvariantSylow
public import CFSG.Assembly.OrderReductions.TwoPointInvolutions

public section

namespace CFSG.OrderReductions.TwoPointSylow

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions
open scoped Pointwise

theorem normalizes_image_of_invariant {group : Type*} [Group group]
    (ambient : Subgroup group) (element : group)
    (normalizes : element ∈ Subgroup.normalizer (ambient : Set group))
    (subgroup : Subgroup ambient)
    (invariant : subgroup.map
      (ambient.normalizerMonoidHom ⟨element, normalizes⟩).toMonoidHom = subgroup) :
    element ∈ Subgroup.normalizer (subgroup.map ambient.subtype : Set group) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (subgroup.map ambient.subtype).map (MulAut.conj element).toMonoidHom =
    subgroup.map ambient.subtype
  have intertwines : (MulAut.conj element).toMonoidHom.comp ambient.subtype =
      ambient.subtype.comp
        (ambient.normalizerMonoidHom ⟨element, normalizes⟩).toMonoidHom := by
    ext original
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe ambient ⟨element, normalizes⟩
      original).symm
  rw [Subgroup.map_map, intertwines, ← Subgroup.map_map, invariant]

theorem exists_sylow_normalizing_flip {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second) (sylow : Sylow prime (pairSubgroup first second)) :
    ∃ flip : Involution group,
      flip.val ∈ Subgroup.normalizer
        ((sylow : Subgroup (pairSubgroup first second)).map
          (pairSubgroup first second).subtype : Set group) ∧
      flip.val • first = second ∧ flip.val • second = first := by
  obtain ⟨original_flip, first_moves, second_moves⟩ :=
    CFSG.OrderReductions.InvolutionFusion.involution_swapping_components first second distinct
  have odd_pair : Odd (Nat.card (pairSubgroup first second)) :=
    distinct_componentStabilizers_odd_intersection first second distinct
  obtain ⟨invariant_sylow, invariant⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_odd prime odd_pair
      (flipAutomorphism first second original_flip first_moves second_moves)
      (flipAutomorphism_involutive first second original_flip first_moves second_moves)
  have original_normalizes := normalizes_image_of_invariant (pairSubgroup first second)
    original_flip.val (flip_normalizes_pair first second original_flip first_moves second_moves)
    (invariant_sylow : Subgroup (pairSubgroup first second)) invariant
  obtain ⟨conjugator, conjugates⟩ := MulAction.exists_smul_eq
    (pairSubgroup first second) invariant_sylow sylow
  have conjugate_image :
      ((invariant_sylow : Subgroup (pairSubgroup first second)).map
        (pairSubgroup first second).subtype).map (MulAut.conj conjugator.val).toMonoidHom =
      (sylow : Subgroup (pairSubgroup first second)).map
        (pairSubgroup first second).subtype := by
    have internal_eq := congrArg
      (fun current : Sylow prime (pairSubgroup first second) =>
        (current : Subgroup (pairSubgroup first second))) conjugates
    have internal_conjugate :
        (invariant_sylow : Subgroup (pairSubgroup first second)).map
          (MulAut.conj conjugator).toMonoidHom = sylow := by
      ext element
      change element ∈ ((conjugator • invariant_sylow :
        Sylow prime (pairSubgroup first second)) : Set (pairSubgroup first second)) ↔ _
      rw [Sylow.coe_smul]
      exact Iff.rfl.trans (SetLike.ext_iff.mp internal_eq element)
    have intertwines : (MulAut.conj conjugator.val).toMonoidHom.comp
        (pairSubgroup first second).subtype = (pairSubgroup first second).subtype.comp
          (MulAut.conj conjugator).toMonoidHom := by
      ext element
      rfl
    rw [Subgroup.map_map, intertwines, ← Subgroup.map_map, internal_conjugate]
  refine ⟨conjugator.val • original_flip, ?_, ?_, ?_⟩
  · rw [involution_smul_val, ← conjugate_image,
      ← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj conjugator.val).bijective]
    exact Subgroup.mem_map_of_mem (MulAut.conj conjugator.val).toMonoidHom original_normalizes
  · rw [involution_smul_val, mul_smul, mul_smul]
    have first_fixed := MulAction.mem_stabilizer_iff.mp conjugator.property.1
    have second_fixed := MulAction.mem_stabilizer_iff.mp conjugator.property.2
    rw [inv_smul_eq_iff.mpr first_fixed.symm, first_moves, second_fixed]
  · rw [involution_smul_val, mul_smul, mul_smul]
    have first_fixed := MulAction.mem_stabilizer_iff.mp conjugator.property.1
    have second_fixed := MulAction.mem_stabilizer_iff.mp conjugator.property.2
    rw [inv_smul_eq_iff.mpr second_fixed.symm, second_moves, first_fixed]

end CFSG.OrderReductions.TwoPointSylow
