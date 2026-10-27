module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite

public section

namespace CFSG.OrderReductions.PrimePart

@[expose] def primePart (prime cardinality : ℕ) : ℕ := prime ^ cardinality.factorization prime

theorem primePart_subgroup_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (smaller larger : Subgroup group)
    (contains : smaller ≤ larger) :
    primePart prime (Nat.card smaller) ≤ primePart prime (Nat.card larger) := by
  have factors := (Nat.factorization_le_iff_dvd
    (ne_of_gt (Nat.card_pos (α := smaller)))
    (ne_of_gt (Nat.card_pos (α := larger)))).mpr (Subgroup.card_dvd_of_le contains)
  exact Nat.pow_le_pow_right (Fact.out : Nat.Prime prime).pos (factors prime)

theorem sylow_map_card_eq_primePart {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (sylow : Sylow prime subgroup) :
    Nat.card ((sylow : Subgroup subgroup).map subgroup.subtype) =
      primePart prime (Nat.card subgroup) := by
  rw [Subgroup.card_map_of_injective Subtype.val_injective, sylow.card_eq_multiplicity]
  rfl

theorem exists_sylow_image_of_card {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup ambient : Subgroup group)
    (contains : subgroup ≤ ambient)
    (card_equal : Nat.card subgroup = primePart prime (Nat.card ambient)) :
    ∃ sylow : Sylow prime ambient,
      (sylow : Subgroup ambient).map ambient.subtype = subgroup := by
  have internal_card : Nat.card (subgroup.subgroupOf ambient) =
      prime ^ (Nat.card ambient).factorization prime := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe contains).toEquiv]
    exact card_equal
  let sylow := Sylow.ofCard (subgroup.subgroupOf ambient) internal_card
  exact ⟨sylow, Subgroup.map_subgroupOf_eq_of_le contains⟩

theorem primePart_eq_iff_contains_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (smaller larger : Subgroup group)
    (contains : smaller ≤ larger) :
    primePart prime (Nat.card smaller) = primePart prime (Nat.card larger) ↔
      ∃ sylow : Sylow prime larger, (sylow : Subgroup larger).map larger.subtype ≤ smaller := by
  constructor
  · intro equal_parts
    obtain ⟨internal⟩ := Sylow.nonempty (p := prime) (G := smaller)
    let image := (internal : Subgroup smaller).map smaller.subtype
    have image_le : image ≤ larger := by
      intro element mem_image
      obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
      exact equal_image ▸ contains original.property
    have image_card : Nat.card image = primePart prime (Nat.card larger) :=
      (sylow_map_card_eq_primePart prime smaller internal).trans equal_parts
    obtain ⟨sylow, equal_image⟩ := exists_sylow_image_of_card prime image larger image_le image_card
    refine ⟨sylow, ?_⟩
    rw [equal_image]
    intro element mem_image
    obtain ⟨original, _, equal_original⟩ := Subgroup.mem_map.mp mem_image
    exact equal_original ▸ original.property
  · rintro ⟨sylow, sylow_le⟩
    apply le_antisymm (primePart_subgroup_le prime smaller larger contains)
    have divides := Subgroup.card_dvd_of_le sylow_le
    rw [sylow_map_card_eq_primePart prime larger sylow] at divides
    have factors := (Nat.factorization_le_iff_dvd
      (pow_ne_zero _ (Fact.out : Nat.Prime prime).ne_zero)
      (ne_of_gt (Nat.card_pos (α := smaller)))).mpr divides
    have exponent_le := factors prime
    rw [Nat.factorization_pow_self (Fact.out : Nat.Prime prime)] at exponent_le
    exact Nat.pow_le_pow_right (Fact.out : Nat.Prime prime).pos exponent_le

theorem primePart_mul (prime first second : ℕ) (first_ne : first ≠ 0) (second_ne : second ≠ 0) :
    primePart prime (first * second) = primePart prime first * primePart prime second := by
  unfold primePart
  rw [Nat.factorization_mul first_ne second_ne, Finsupp.add_apply, pow_add]

theorem primePart_card_mul_index {group : Type*} [Group group] [Finite group]
    (prime : ℕ) (subgroup : Subgroup group) :
    primePart prime (Nat.card subgroup) * primePart prime subgroup.index =
      primePart prime (Nat.card group) := by
  have subgroup_ne := ne_of_gt (Nat.card_pos (α := subgroup))
  have index_ne : subgroup.index ≠ 0 := by
    intro zero_index
    have card_eq := subgroup.card_mul_index
    rw [zero_index, mul_zero] at card_eq
    exact ne_of_gt (Nat.card_pos (α := group)) card_eq.symm
  rw [← primePart_mul prime (Nat.card subgroup) subgroup.index subgroup_ne index_ne,
    subgroup.card_mul_index]

theorem eq_top_of_contains_sylow_for_every_prime {group : Type*}
    [Group group] [Finite group] (subgroup : Subgroup group)
    (contains : ∀ prime : ℕ, Nat.Prime prime →
      ∃ sylow : Sylow prime group, (sylow : Subgroup group) ≤ subgroup) :
    subgroup = ⊤ := by
  have group_nonzero : Nat.card group ≠ 0 := ne_of_gt Nat.card_pos
  have subgroup_nonzero : Nat.card subgroup ≠ 0 := ne_of_gt Nat.card_pos
  have full_divides : Nat.card group ∣ Nat.card subgroup := by
    apply (Nat.factorization_le_iff_dvd group_nonzero subgroup_nonzero).mp
    intro prime
    by_cases prime_is_prime : Nat.Prime prime
    · have : Fact (Nat.Prime prime) := ⟨prime_is_prime⟩
      obtain ⟨sylow, sylow_le⟩ := contains prime prime_is_prime
      have divides := Subgroup.card_dvd_of_le sylow_le
      rw [sylow.card_eq_multiplicity] at divides
      exact (prime_is_prime.pow_dvd_iff_le_factorization subgroup_nonzero).mp divides
    · rw [Nat.factorization_eq_zero_of_not_prime _ prime_is_prime]
      exact Nat.zero_le _
  exact subgroup.eq_top_of_card_eq
    (Nat.dvd_antisymm subgroup.card_subgroup_dvd_card full_divides)

end CFSG.OrderReductions.PrimePart
