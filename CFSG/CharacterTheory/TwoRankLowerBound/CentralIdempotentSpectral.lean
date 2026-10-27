module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterIdempotents

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def characterIdempotentExpansion {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficient : basis.index → ℂ) :
    MonoidAlgebra ℂ G :=
  ∑ label, coefficient label • complexCharacterIdempotent (basis.representation label).character

theorem characterIdempotentExpansion_central {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficient : basis.index → ℂ) :
    ∀ other : MonoidAlgebra ℂ G, Commute (characterIdempotentExpansion basis coefficient) other := by
  intro other
  apply Commute.sum_left
  intro label _
  exact (complexCharacterIdempotent_central (basis.representation label) other).smul_left _

theorem characterIdempotentExpansion_action {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficient : basis.index → ℂ)
    (target : basis.index) :
    (basis.representation target).representation.asAlgebraHom
      (characterIdempotentExpansion basis coefficient) =
      coefficient target • (1 : Module.End ℂ (basis.representation target).vector) := by
  simp only [characterIdempotentExpansion, map_sum, map_smul,
    complexCharacterIdempotent_irreducible_action _ _ (basis.irreducible _) (basis.irreducible target)]
  simp [basis.distinct.eq_iff]

theorem irreducible_scalar_identity_injective {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible) :
    Function.Injective (fun scalar : ℂ => scalar • (1 : Module.End ℂ data.vector)) := by
  intro left right hequal
  have htrace := congrArg (LinearMap.trace ℂ data.vector) hequal
  simp only [map_smul, LinearMap.trace_one, ← Representation.char_one data.representation,
    smul_eq_mul] at htrace
  exact mul_right_cancel₀ (irreducible_character_degree_ne_zero data hirreducible) htrace

theorem characterIdempotentExpansion_injective {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    Function.Injective (characterIdempotentExpansion basis) := by
  intro left right hequal
  funext label
  have haction := congrArg (basis.representation label).representation.asAlgebraHom hequal
  rw [characterIdempotentExpansion_action, characterIdempotentExpansion_action] at haction
  exact irreducible_scalar_identity_injective (basis.representation label) (basis.irreducible label) haction

@[expose] noncomputable def centralCharacterScalar {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (algebraElement : MonoidAlgebra ℂ G)
    (label : basis.index) : ℂ :=
  (Nat.card G : ℂ) * characterPairing (fun element => algebraElement.coeff element⁻¹)
    (basis.representation label).character / (basis.representation label).character 1

theorem centralCharacterScalar_action {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (algebraElement : MonoidAlgebra ℂ G)
    (hcentral : ∀ other : MonoidAlgebra ℂ G, Commute algebraElement other)
    (label : basis.index) :
    (basis.representation label).representation.asAlgebraHom algebraElement =
      centralCharacterScalar basis algebraElement label •
        (1 : Module.End ℂ (basis.representation label).vector) := by
  conv_lhs => rw [← groupAlgebraClassElement_of_coeff algebraElement, groupAlgebraClassElement_action]
  apply irreducible_weightedCharacterOperator_formula _ (basis.irreducible label)
  intro element conjugator
  have hinverse : (conjugator * element * conjugator⁻¹)⁻¹ =
      conjugator * element⁻¹ * conjugator⁻¹ := by group
  rw [hinverse]
  exact central_groupAlgebra_coeff_conjugation algebraElement hcentral element⁻¹ conjugator

theorem centralCharacterScalar_reconstruction {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (algebraElement : MonoidAlgebra ℂ G)
    (hcentral : ∀ other : MonoidAlgebra ℂ G, Commute algebraElement other) :
    algebraElement = characterIdempotentExpansion basis (centralCharacterScalar basis algebraElement) := by
  apply sub_eq_zero.mp
  apply central_groupAlgebra_eq_zero_of_basis_actions basis
  · intro other
    exact (hcentral other).sub_left (characterIdempotentExpansion_central _ _ other)
  · intro label
    rw [map_sub, centralCharacterScalar_action basis algebraElement hcentral,
      characterIdempotentExpansion_action, sub_self]

theorem characterIdempotentExpansion_mul {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (left right : basis.index → ℂ) :
    characterIdempotentExpansion basis left * characterIdempotentExpansion basis right =
      characterIdempotentExpansion basis (fun label => left label * right label) := by
  apply sub_eq_zero.mp
  apply central_groupAlgebra_eq_zero_of_basis_actions basis
  · intro other
    exact ((characterIdempotentExpansion_central _ _ other).mul_left
      (characterIdempotentExpansion_central _ _ other)).sub_left
      (characterIdempotentExpansion_central _ _ other)
  · intro label
    rw [map_sub, map_mul, characterIdempotentExpansion_action,
      characterIdempotentExpansion_action, characterIdempotentExpansion_action,
      smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, sub_self]

theorem characterIdempotentExpansion_one {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    characterIdempotentExpansion basis (fun _ => 1) = 1 := by
  apply sub_eq_zero.mp
  apply central_groupAlgebra_eq_zero_of_basis_actions basis
  · intro other
    exact (characterIdempotentExpansion_central _ _ other).sub_left (Commute.one_left _)
  · intro label
    rw [map_sub, characterIdempotentExpansion_action, one_smul, map_one, sub_self]

theorem central_idempotent_scalar_zero_or_one {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (algebraElement : MonoidAlgebra ℂ G)
    (hcentral : ∀ other : MonoidAlgebra ℂ G, Commute algebraElement other)
    (hidempotent : IsIdempotentElem algebraElement) (label : basis.index) :
    centralCharacterScalar basis algebraElement label = 0 ∨
      centralCharacterScalar basis algebraElement label = 1 := by
  have haction := congrArg (basis.representation label).representation.asAlgebraHom hidempotent.eq
  rw [map_mul, centralCharacterScalar_action basis algebraElement hcentral,
    smul_mul_assoc, mul_smul_comm, one_mul, smul_smul] at haction
  have hscalar := irreducible_scalar_identity_injective (basis.representation label)
    (basis.irreducible label) haction
  have hproduct : centralCharacterScalar basis algebraElement label *
      (centralCharacterScalar basis algebraElement label - 1) = 0 := by
    linear_combination hscalar
  exact (mul_eq_zero.mp hproduct).imp id sub_eq_zero.mp

@[expose] noncomputable def characterSubsetIdempotent {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) : MonoidAlgebra ℂ G :=
  characterIdempotentExpansion basis (fun label => if label ∈ support then 1 else 0)

theorem characterIdempotentExpansion_sub {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (left right : basis.index → ℂ) :
    characterIdempotentExpansion basis (left - right) =
      characterIdempotentExpansion basis left - characterIdempotentExpansion basis right := by
  simp only [characterIdempotentExpansion, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem characterIdempotentExpansion_add {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (left right : basis.index → ℂ) :
    characterIdempotentExpansion basis (left + right) =
      characterIdempotentExpansion basis left + characterIdempotentExpansion basis right := by
  simp only [characterIdempotentExpansion, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem characterSubsetIdempotent_union {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (left right : Finset basis.index) :
    characterSubsetIdempotent basis (left ∪ right) =
      characterSubsetIdempotent basis left + characterSubsetIdempotent basis right -
        characterSubsetIdempotent basis (left ∩ right) := by
  simp only [characterSubsetIdempotent, ← characterIdempotentExpansion_sub,
    ← characterIdempotentExpansion_add]
  congr 1
  funext label
  by_cases hleft : label ∈ left <;> by_cases hright : label ∈ right <;> simp [hleft, hright]

theorem characterSubsetIdempotent_union_disjoint {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (left right : Finset basis.index)
    (hdisjoint : Disjoint left right) :
    characterSubsetIdempotent basis (left ∪ right) =
      characterSubsetIdempotent basis left + characterSubsetIdempotent basis right := by
  have hintersection : left ∩ right = ∅ := disjoint_iff_inf_le.mp hdisjoint |>
    le_bot_iff.mp
  rw [characterSubsetIdempotent_union, hintersection]
  simp only [characterSubsetIdempotent, characterIdempotentExpansion, Finset.notMem_empty,
    ite_false, zero_smul, Finset.sum_const_zero, sub_zero]

theorem characterSubsetIdempotent_central {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    ∀ other : MonoidAlgebra ℂ G, Commute (characterSubsetIdempotent basis support) other :=
  characterIdempotentExpansion_central basis _

theorem characterSubsetIdempotent_injective {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    Function.Injective (characterSubsetIdempotent basis) := by
  intro left right hequal
  have hcoefficient := characterIdempotentExpansion_injective basis hequal
  ext label
  have hlabel := congrFun hcoefficient label
  by_cases hleft : label ∈ left <;> by_cases hright : label ∈ right <;>
    simp [hleft, hright] at hlabel ⊢

theorem characterSubsetIdempotent_inter {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (left right : Finset basis.index) :
    characterSubsetIdempotent basis (left ∩ right) =
      characterSubsetIdempotent basis left * characterSubsetIdempotent basis right := by
  rw [characterSubsetIdempotent, characterSubsetIdempotent, characterSubsetIdempotent,
    characterIdempotentExpansion_mul]
  congr 1
  funext label
  by_cases hleft : label ∈ left <;> by_cases hright : label ∈ right <;> simp [hleft, hright]

theorem characterSubsetIdempotent_compl {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    characterSubsetIdempotent basis supportᶜ = 1 - characterSubsetIdempotent basis support := by
  rw [← characterIdempotentExpansion_one basis, characterSubsetIdempotent,
    characterSubsetIdempotent, ← characterIdempotentExpansion_sub]
  congr 1
  funext label
  by_cases hmember : label ∈ support <;> simp [hmember]

theorem characterSubsetIdempotent_empty {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) : characterSubsetIdempotent basis ∅ = 0 := by
  simp only [characterSubsetIdempotent, characterIdempotentExpansion, Finset.notMem_empty,
    ite_false, zero_smul, Finset.sum_const_zero]

theorem characterSubsetIdempotent_univ {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) : characterSubsetIdempotent basis Finset.univ = 1 := by
  simpa only [characterSubsetIdempotent, Finset.mem_univ, ite_true] using
    characterIdempotentExpansion_one basis

theorem characterSubsetIdempotent_isIdempotent {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    IsIdempotentElem (characterSubsetIdempotent basis support) := by
  rw [isIdempotentElem_iff, ← characterSubsetIdempotent_inter, Finset.inter_self]

theorem central_idempotent_eq_character_subset {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (algebraElement : MonoidAlgebra ℂ G)
    (hcentral : ∀ other : MonoidAlgebra ℂ G, Commute algebraElement other)
    (hidempotent : IsIdempotentElem algebraElement) :
    ∃! support : Finset basis.index, algebraElement = characterSubsetIdempotent basis support := by
  let support := Finset.univ.filter (fun label => centralCharacterScalar basis algebraElement label = 1)
  have hcoefficient : centralCharacterScalar basis algebraElement =
      fun label => if label ∈ support then 1 else 0 := by
    funext label
    rcases central_idempotent_scalar_zero_or_one basis algebraElement hcentral hidempotent label with
      hzero | hone
    · simp [support, hzero]
    · simp [support, hone]
  refine ⟨support, ?_, ?_⟩
  · rw [centralCharacterScalar_reconstruction basis algebraElement hcentral, hcoefficient]
    rfl
  · intro other hother
    have hequal := characterIdempotentExpansion_injective basis
      ((centralCharacterScalar_reconstruction basis algebraElement hcentral).symm.trans hother)
    ext label
    have hlabel := congrFun hequal label
    rw [hcoefficient] at hlabel
    by_cases hotherMember : label ∈ other <;> by_cases hsupportMember : label ∈ support <;>
      simp [hotherMember, hsupportMember] at hlabel ⊢

end CFSG.TwoRankLowerBound.Helpers
