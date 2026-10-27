module

public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualCharacters

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe groupUniverse vectorUniverse

theorem characterPairing_distinct_expansion_coefficient
    {G : Type groupUniverse} [Group G] [Fintype G] {index : Type*} [Fintype index]
    (representation : index → FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G)
    (hirreducible : ∀ label, (representation label).IsIrreducible)
    (hdistinct : Function.Injective (fun label => (representation label).character))
    (coefficient : index → ℂ) (target : index) :
    characterPairing
      (fun element => ∑ label, coefficient label * (representation label).character element)
      (representation target).character = coefficient target := by
  rw [characterPairing_expansion_left]
  simp_rw [characterPairing_irreducible _ _ (hirreducible _) (hirreducible target)]
  simp [hdistinct.eq_iff]

theorem characterPairing_distinct_expansion_norm
    {G : Type groupUniverse} [Group G] [Fintype G] {index : Type*} [Fintype index]
    (representation : index → FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G)
    (hirreducible : ∀ label, (representation label).IsIrreducible)
    (hdistinct : Function.Injective (fun label => (representation label).character))
    (coefficient : index → ℂ) :
    characterPairing
      (fun element => ∑ label, coefficient label * (representation label).character element)
      (fun element => ∑ label, coefficient label * (representation label).character element) =
      ∑ label, coefficient label ^ 2 := by
  rw [characterPairing_expansion_right]
  simp_rw [characterPairing_distinct_expansion_coefficient representation hirreducible hdistinct]
  simp only [pow_two]

theorem characterPairing_irreducible_expansion_principal
    {G : Type groupUniverse} [Group G] [Fintype G] {index : Type*} [Fintype index]
    (representation : index → FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G)
    (hirreducible : ∀ label, (representation label).IsIrreducible)
    (coefficient : index → ℂ) :
    characterPairing
      (fun element => ∑ label, coefficient label * (representation label).character element) 1 =
      ∑ label, if (representation label).character = 1 then coefficient label else 0 := by
  rw [characterPairing_expansion_left]
  apply Finset.sum_congr rfl
  intro label _
  have hpair := characterPairing_irreducible (representation label)
    (principalFiniteComplexRepresentation G) (hirreducible label)
    (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hpair
  rw [hpair]
  split_ifs <;> simp

structure IrreducibleCharacterExpansion (G : Type groupUniverse) [Group G]
    (function : G → ℂ) where
  index : Type groupUniverse
  [fintype : Fintype index]
  representation : index → FiniteComplexRepresentation.{groupUniverse, groupUniverse} G
  irreducible : ∀ label, (representation label).IsIrreducible
  distinct : Function.Injective (fun label => (representation label).character)
  coefficient : index → ℤ
  expansion : ∀ element : G,
    function element = ∑ label, (coefficient label : ℂ) * (representation label).character element

attribute [instance] IrreducibleCharacterExpansion.fintype

set_option backward.isDefEq.respectTransparency false in
theorem virtualCharacter_exists_irreducibleCharacterExpansion
    {G : Type groupUniverse} [Group G] [Finite G] {function : G → ℂ}
    (hvirtual : function ∈ virtualCharacters G) :
    Nonempty (IrreducibleCharacterExpansion G function) := by
  obtain ⟨support, coefficient, hsupport, hsum⟩ :=
    virtualCharacter_exists_distinct_irreducible_expansion hvirtual
  choose representation hirreducible hequal using (fun label : support =>
    hsupport label label.property)
  refine ⟨{
    index := support
    representation := representation
    irreducible := hirreducible
    distinct := ?_
    coefficient := fun label => coefficient label
    expansion := ?_ }⟩
  · intro left right heq
    apply Subtype.ext
    rw [← hequal left, ← hequal right]
    exact heq
  · intro element
    rw [hsum, Finset.sum_subtype support (by intros; rfl)]
    apply Finset.sum_congr rfl
    intro label _
    rw [hequal label]

theorem characterPairing_constant_one {G : Type*} [Group G] [Fintype G] (constant : ℂ) :
    characterPairing (fun _element : G => constant) 1 = constant := by
  unfold characterPairing
  simp only [Pi.one_apply, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

theorem irreducible_character_ne_one_has_nontrivial_action
    {G : Type groupUniverse} [Group G] [Fintype G]
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G)
    (hirreducible : data.IsIrreducible) (hnonprincipal : data.character ≠ 1) :
    ∃ element : G, data.representation element ≠ 1 := by
  by_contra! htrivial
  have hconstant : data.character = fun _element : G => data.character 1 := by
    ext element
    simp only [FiniteComplexRepresentation.character, Representation.character, htrivial]
  have hzero := characterPairing_irreducible data (principalFiniteComplexRepresentation G)
    hirreducible (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character, ite_eq_right hnonprincipal,
    hconstant, characterPairing_constant_one] at hzero
  exact irreducible_character_degree_ne_zero data hirreducible hzero

theorem expansion_exists_principal_of_pairing_one {G : Type groupUniverse}
    [Group G] [Fintype G] {function : G → ℂ}
    (data : IrreducibleCharacterExpansion G function)
    (hpair : characterPairing function 1 = 1) :
    ∃ principal : data.index,
      (data.representation principal).character = 1 ∧ data.coefficient principal = 1 := by
  have hexpansion : function = fun element => ∑ label,
      (data.coefficient label : ℂ) * (data.representation label).character element :=
    funext data.expansion
  rw [hexpansion, characterPairing_irreducible_expansion_principal
    data.representation data.irreducible] at hpair
  have hexists : ∃ principal : data.index, (data.representation principal).character = 1 := by
    by_contra! hnone
    simp [hnone] at hpair
  obtain ⟨principal, hprincipal⟩ := hexists
  have hequiv : ∀ label : data.index,
      (data.representation label).character = 1 ↔ label = principal := by
    intro label
    rw [← hprincipal, data.distinct.eq_iff]
  simp only [hequiv, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hpair
  exact ⟨principal, hprincipal, by exact_mod_cast hpair⟩

theorem expansion_integer_norm_of_pairing_three {G : Type groupUniverse}
    [Group G] [Fintype G] {function : G → ℂ}
    (data : IrreducibleCharacterExpansion G function)
    (hnorm : characterPairing function function = 3) :
    ∑ label, data.coefficient label ^ 2 = 3 := by
  have hexpansion : function = fun element => ∑ label,
      (data.coefficient label : ℂ) * (data.representation label).character element :=
    funext data.expansion
  rw [hexpansion, characterPairing_distinct_expansion_norm
    data.representation data.irreducible data.distinct] at hnorm
  exact_mod_cast hnorm

end CFSG.TwoRankLowerBound.Helpers
