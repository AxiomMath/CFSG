module

public import CFSG.Assembly.OrderReductions.CharacterSpan

public section

namespace CFSG.OrderReductions.CharacterInflation

open CFSG.OrderReductions.CharacterCoefficients
open CFSG.OrderReductions.CharacterSpan
open scoped Classical

universe level

theorem fiber_card {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism) (element : target) :
    Nat.card {current : source // homomorphism current = element} = Nat.card homomorphism.ker := by
  obtain ⟨preimage, equal⟩ := surjective element
  rw [← equal]
  exact Nat.card_congr (homomorphism.fiberEquivKer preimage)

theorem sum_comp_surjective {field source target : Type*} [Field field] [Group source] [Group target]
    [Fintype source] [Fintype target] (homomorphism : source →* target)
    (surjective : Function.Surjective homomorphism) (function : target → field) :
    (∑ element : source, function (homomorphism element)) =
      (Nat.card homomorphism.ker : field) * ∑ element : target, function element := by
  rw [← Fintype.sum_fiberwise' homomorphism function]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    fiber_card homomorphism surjective, ← Finset.mul_sum]

theorem cardinality_eq {field source target : Type*} [Field field] [Group source] [Group target]
    [Fintype source] [Fintype target] (homomorphism : source →* target)
    (surjective : Function.Surjective homomorphism) :
    (Nat.card source : field) = (Nat.card homomorphism.ker : field) * (Nat.card target : field) := by
  have equal := sum_comp_surjective homomorphism surjective (fun _ => (1 : field))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, mul_one] using equal

theorem scalarProduct_comp_surjective {field source target : Type*} [Field field] [CharZero field]
    [Group source] [Group target] [Fintype source] [Fintype target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (first second : target → field) :
    scalarProduct (first ∘ homomorphism) (second ∘ homomorphism) = scalarProduct first second := by
  have kernel_card_ne_zero : (Nat.card homomorphism.ker : field) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)
  have target_card_ne_zero : (Nat.card target : field) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)
  simp only [scalarProduct, Function.comp_apply, map_inv]
  rw [sum_comp_surjective homomorphism surjective (fun element => first element * second element⁻¹),
    cardinality_eq homomorphism surjective]
  field_simp

theorem comp_mem_virtualCharacters {field source target : Type level} [Field field] [CharZero field]
    [Group source] [Group target] [Finite source] (homomorphism : source →* target)
    (function : target → field) (virtuality : function ∈ virtualCharacters field target) :
    function ∘ homomorphism ∈ virtualCharacters field source := by
  induction virtuality using Submodule.span_induction with
  | mem function membership =>
      obtain ⟨representation, _, character_eq⟩ := membership
      rw [← character_eq]
      exact character_mem_virtualCharacters (representation.ρ.comp homomorphism)
  | zero =>
      exact (virtualCharacters field source).zero_mem
  | add first second _ _ first_mem second_mem =>
      exact (virtualCharacters field source).add_mem first_mem second_mem
  | smul coefficient function _ membership =>
      exact (virtualCharacters field source).smul_mem coefficient membership

end CFSG.OrderReductions.CharacterInflation
