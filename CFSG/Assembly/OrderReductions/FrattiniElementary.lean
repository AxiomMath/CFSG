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
public import CFSG.Assembly.OrderReductions.Helpers
public import CFSG.Assembly.OrderReductions.InvertedSubgroup

public section

namespace CFSG.OrderReductions.FrattiniElementary

theorem maximal_prime_subgroup_normal {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group)
    (maximal : Subgroup group) (coatom : IsCoatom maximal) : maximal.Normal := by
  have := prime_group.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom maximal Group.normalizerCondition_of_isNilpotent coatom

theorem maximal_prime_quotient_card {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group)
    (maximal : Subgroup group) (coatom : IsCoatom maximal) [maximal.Normal] :
    Nat.card (group ⧸ maximal) = prime := by
  let projection := QuotientGroup.mk' maximal
  have quotient_nontrivial : Nontrivial (group ⧸ maximal) :=
    QuotientGroup.nontrivial_iff.mpr coatom.ne_top
  have simple : IsSimpleGroup (group ⧸ maximal) := by
    constructor
    intro normal _
    by_cases normal_bot : normal = ⊥
    · exact Or.inl normal_bot
    · right
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective maximal)
      rw [Subgroup.comap_top]
      apply coatom.lt_iff.mp
      apply lt_of_le_of_ne (QuotientGroup.le_comap_mk' maximal normal)
      intro equal
      apply normal_bot
      have image := congrArg (Subgroup.map projection) equal
      rw [QuotientGroup.map_mk'_self, Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective maximal)] at image
      exact image.symm
  have quotient_prime := prime_group.to_quotient maximal
  have := quotient_prime.isNilpotent
  have : Group.IsSolvable (group ⧸ maximal) := inferInstance
  have : IsMulCommutative (group ⧸ maximal) :=
    CFSG.OrderReductions.Helpers.simple_solvable_isMulCommutative _
  have card_prime := CFSG.OrderReductions.Helpers.prime_card_of_simple_commutative (group ⧸ maximal)
  obtain ⟨exponent, card_eq⟩ := quotient_prime.exists_card_eq
  have prime_divides : prime ∣ Nat.card (group ⧸ maximal) := by
    have exponent_pos : 0 < exponent := by
      by_contra nonpositive
      have exponent_zero : exponent = 0 := by omega
      rw [exponent_zero, pow_zero] at card_eq
      exact card_prime.ne_one card_eq
    rw [card_eq]
    exact dvd_pow_self prime (Nat.ne_of_gt exponent_pos)
  exact (card_prime.dvd_iff_eq (Fact.out : Nat.Prime prime).ne_one).mp prime_divides

theorem pow_mem_frattini {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group)
    (element : group) : element ^ prime ∈ frattini group := by
  change element ^ prime ∈ ⨅ maximal : Subgroup group, ⨅ (_ : IsCoatom maximal), maximal
  simp only [Subgroup.mem_iInf]
  intro maximal coatom
  have : maximal.Normal := maximal_prime_subgroup_normal prime prime_group maximal coatom
  have card_eq := maximal_prime_quotient_card prime prime_group maximal coatom
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' maximal (element ^ prime) = 1
  rw [map_pow, ← card_eq]
  exact pow_card_eq_one'

theorem commutator_le_frattini {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group) :
    commutator group ≤ frattini group := by
  intro element membership
  change element ∈ ⨅ maximal : Subgroup group, ⨅ (_ : IsCoatom maximal), maximal
  simp only [Subgroup.mem_iInf]
  intro maximal coatom
  have : maximal.Normal := maximal_prime_subgroup_normal prime prime_group maximal coatom
  let projection := QuotientGroup.mk' maximal
  have : IsCyclic (group ⧸ maximal) :=
    isCyclic_of_prime_card (maximal_prime_quotient_card prime prime_group maximal coatom)
  have quotient_commutator : commutator (group ⧸ maximal) = ⊥ :=
    (commutator_eq_bot_iff _).mpr inferInstance
  have image_commutator : (commutator group).map projection = commutator (group ⧸ maximal) := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective maximal)]
    rfl
  have image_mem : projection element ∈ (commutator group).map projection :=
    Subgroup.mem_map.mpr ⟨element, membership, rfl⟩
  rw [image_commutator, quotient_commutator] at image_mem
  exact (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp image_mem)

theorem frattini_quotient_isMulCommutative {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group) :
    IsMulCommutative (group ⧸ frattini group) := by
  apply (commutator_eq_bot_iff _).mp
  let projection := QuotientGroup.mk' (frattini group)
  have image_eq : (commutator group).map projection = commutator (group ⧸ frattini group) := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (frattini group))]
    rfl
  rw [← image_eq]
  apply le_bot_iff.mp
  rw [Subgroup.map_le_iff_le_comap]
  change commutator group ≤ projection.ker
  rw [QuotientGroup.ker_mk']
  exact commutator_le_frattini prime prime_group

theorem frattini_quotient_exponent {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group)
    (element : group ⧸ frattini group) : element ^ prime = 1 := by
  obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective (frattini group) element
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (pow_mem_frattini prime prime_group original)

end CFSG.OrderReductions.FrattiniElementary
