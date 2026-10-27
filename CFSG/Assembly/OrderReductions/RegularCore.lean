module

public import CFSG.Assembly.OrderReductions.SolvableComplementContainment
public import CFSG.Assembly.OrderReductions.PrimeRegular

public section

namespace CFSG.OrderReductions.RegularCore

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.InvolutiveIntersection
open CFSG.OrderReductions.PrimeComplementCore

theorem ambientCore_invariant {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (subgroup : Subgroup group) (invariant : subgroup.map automorphism.toMonoidHom = subgroup) :
    (ambientCore prime subgroup).map automorphism.toMonoidHom = ambientCore prime subgroup := by
  rw [ambientCore_map_equiv, invariant]

theorem intersection_core_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (subgroup : Subgroup group) [Group.IsSolvable subgroup]
    (full_primePart : CFSG.OrderReductions.PrimePart.primePart prime
      (Nat.card (intersection automorphism subgroup)) =
        CFSG.OrderReductions.PrimePart.primePart prime (Nat.card subgroup)) :
    ambientCore prime (intersection automorphism subgroup) ≤ ambientCore prime subgroup :=
  CFSG.OrderReductions.SolvableComplementContainment.full_primePart_ambientCore_le prime _ _
    inf_le_left full_primePart

theorem core_invariant_of_equal_intersection {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (subgroup : Subgroup group)
    (core_eq : ambientCore prime (intersection automorphism subgroup) = ambientCore prime subgroup) :
    (ambientCore prime subgroup).map automorphism.toMonoidHom = ambientCore prime subgroup := by
  rw [← core_eq]
  exact ambientCore_invariant prime automorphism _ (intersection_invariant automorphism involutive subgroup)

theorem regular_pair_intersection_core_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second)
    [Group.IsSolvable (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)]
    (regular : CFSG.OrderReductions.PrimeRegular.PRegular prime
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) (componentStabilizer first))
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first) :
    ambientCore prime (intersection (MulAut.conj involution.val)
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)) ≤
        ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) := by
  exact intersection_core_le prime (MulAut.conj involution.val) _
    ((CFSG.OrderReductions.PrimeRegular.pRegular_pair_iff_every_involution
      prime first second distinct).mp regular involution mem_first)

theorem regular_pair_equal_core_invariant_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second)
    (regular : CFSG.OrderReductions.PrimeRegular.PRegular prime
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) (componentStabilizer first))
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first)
    (core_eq : ambientCore prime (intersection (MulAut.conj involution.val)
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)) =
        ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)) :
    involution.val ∈ Subgroup.normalizer
      (ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) : Set group) ∧
      ∃ sylow : Sylow prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second),
        involution.val ∈ Subgroup.normalizer
          (↑((sylow : Subgroup (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).map
            (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second).subtype) : Set group) := by
  refine ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_, ?_⟩
  · exact core_invariant_of_equal_intersection prime (MulAut.conj involution.val)
      (CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive involution) _ core_eq
  · exact CFSG.OrderReductions.PrimeRegular.pRegular_pair_every_involution_invariant_sylow
      prime first second distinct regular involution mem_first

theorem equal_core_nontrivial_normalizer_data {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (flip inside : Involution group) (first_moves : flip.val • first = second)
    (second_moves : flip.val • second = first)
    (core_eq : ambientCore prime (intersection (MulAut.conj inside.val)
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)) =
        ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second))
    (nontrivial : ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) ≠ ⊥) :
    ∃ normal : Subgroup group, normal ≠ ⊥ ∧
      normal ≤ CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second ∧
      (normal.subgroupOf (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).Normal ∧
      flip.val ∈ Subgroup.normalizer (normal : Set group) ∧
      inside.val ∈ Subgroup.normalizer (normal : Set group) := by
  let normal := ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
  refine ⟨normal, nontrivial, ambientCore_le prime _, ambientCore_normal_in_subgroup prime _, ?_, ?_⟩
  · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact ambientCore_invariant prime (MulAut.conj flip.val) _
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (CFSG.OrderReductions.TwoPointInvolutions.flip_normalizes_pair first second flip first_moves second_moves))
  · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact core_invariant_of_equal_intersection prime (MulAut.conj inside.val)
      (CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive inside) _ core_eq

theorem characteristic_pair_image_normalizes {group : Type*} [Group group]
    (pair : Subgroup group) (characteristic : Subgroup pair) [characteristic.Characteristic]
    (element : group) (normalizes : element ∈ Subgroup.normalizer (pair : Set group)) :
    element ∈ Subgroup.normalizer (characteristic.map pair.subtype : Set group) := by
  exact CFSG.OrderReductions.TwoPointSylow.normalizes_image_of_invariant pair element normalizes characteristic
    (Subgroup.characteristic_iff_map_eq.mp inferInstance (pair.normalizerMonoidHom ⟨element, normalizes⟩))

end CFSG.OrderReductions.RegularCore
