module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.SchurAveraging
public import CFSG.CharacterTheory.BlockSectionOrthogonality.Characters
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

attribute [local instance] Classical.propDecidable

@[expose] noncomputable def coefficientElement {G : Type} [Group G] [Fintype G]
    (coefficient : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ element, MonoidAlgebra.single element (coefficient element)

@[simp] theorem coefficientElement_apply {G : Type} [Group G] [Fintype G]
    (coefficient : G → ℂ) (element : G) : (coefficientElement coefficient).coeff element =
      coefficient element := by
  classical
  simp [coefficientElement, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem representation_coefficientElement {G : Type} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    (representation : Representation ℂ G space) (coefficient : G → ℂ) :
    representation.asAlgebraHom (coefficientElement coefficient) =
      ∑ element, coefficient element • representation element := by
  simp [coefficientElement, Representation.asAlgebraHom_single]

@[expose] noncomputable def characterIdempotent {G : Type} [Group G] [Fintype G]
    (character : G → ℂ) : MonoidAlgebra ℂ G :=
  coefficientElement (fun element => character 1 / (Nat.card G : ℂ) * character element⁻¹)

theorem representation_characterIdempotent {G : Type} [Group G] [Fintype G]
    {space : Type} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) [representation.IsIrreducible]
    {character : G → ℂ} (hcharacter : character ∈ BlocksIrr G) :
    representation.asAlgebraHom (characterIdempotent character) =
      if representation.character = character then LinearMap.id else 0 := by
  classical
  have hRepresentation : representation.character ∈ BlocksIrr G :=
    ⟨space, inferInstance, inferInstance, inferInstance, representation, inferInstance, rfl⟩
  have hPair := irreducible_characterPairing hRepresentation hcharacter
  change (Nat.card G : ℂ)⁻¹ * ∑ element,
    representation.character element * character element⁻¹ = _ at hPair
  have hSum : ∑ element, character element⁻¹ * representation.character element =
      (Nat.card G : ℂ) * (if representation.character = character then 1 else 0) := by
    have hCard : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hScaled := congrArg (fun value : ℂ => (Nat.card G : ℂ) * value) hPair
    simpa only [← mul_assoc, mul_inv_cancel₀ hCard, one_mul, mul_comm] using hScaled
  unfold characterIdempotent
  rw [representation_coefficientElement]
  simp only [mul_smul]
  rw [← Finset.smul_sum]
  change (character 1 / (Nat.card G : ℂ)) •
    weightedCharacterOperator representation character = _
  rw [weightedCharacterOperator_eq_scalar representation character
    (irreducible_isClassFunction hcharacter), hSum, smul_smul]
  by_cases hEqual : representation.character = character
  · rw [ite_eq_left hEqual, ite_eq_left hEqual, mul_one, ← hEqual]
    have hCard : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hDegree := irreducible_character_one_ne_zero representation
    field_simp
    exact one_smul _ _
  · simp [hEqual]

set_option backward.isDefEq.respectTransparency false in
theorem irreducible_actions_detect_zero {G : Type} [Group G] [Fintype G]
    (element : MonoidAlgebra ℂ G)
    (hzero : ∀ (space : Type) [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
      (representation : Representation ℂ G space) [representation.IsIrreducible],
      representation.asAlgebraHom element = 0) : element = 0 := by
  classical
  let : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  have hSimple : ∀ simple : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) simple →
      ∀ vector : simple, element • vector = 0 := by
    intro simple hSimple vector
    let := hSimple
    let : Module ℂ simple := (simple.restrictScalars ℂ).module
    let : Module ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) simple) :=
      RestrictScalars.module ℂ (MonoidAlgebra ℂ G) simple
    let representation := Representation.ofModule (k := ℂ) (G := G) simple
    let : representation.IsIrreducible :=
      (Representation.isSimpleModule_iff_irreducible_ofModule simple).mp hSimple
    let inclusion : RestrictScalars ℂ (MonoidAlgebra ℂ G) simple →ₗ[ℂ]
        MonoidAlgebra ℂ G :=
      { toFun := fun value => ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) simple) value).val
        map_add' := by intros; rfl
        map_smul' := by
          intro scalar vector
          rw [RestrictScalars.addEquiv_map_smul]
          change (algebraMap ℂ (MonoidAlgebra ℂ G) scalar) * _ = scalar • _
          rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] }
    let : FiniteDimensional ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) simple) :=
      FiniteDimensional.of_injective inclusion (by
        intro left right hEqual
        apply (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) simple).injective
        exact Subtype.ext hEqual)
    have hAction := congrArg (fun operator : Module.End ℂ
      (RestrictScalars ℂ (MonoidAlgebra ℂ G) simple) => operator
      ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) simple).symm vector))
      (hzero _ representation)
    dsimp [representation] at hAction
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at hAction
    simpa using hAction
  have hSimpleSpan := IsSemisimpleModule.sSup_simples_le
    (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
  have hAnnihilates : ∀ vector : MonoidAlgebra ℂ G, element * vector = 0 := by
    intro vector
    have hMember : vector ∈ (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :=
      Submodule.mem_top
    rw [← hSimpleSpan] at hMember
    rw [sSup_eq_iSup'] at hMember
    refine Submodule.iSup_induction _ (motive := fun vector => element * vector = 0)
      hMember ?_ ?_ ?_
    · intro simple vector hVector
      have hAction := hSimple simple.val simple.property.1 ⟨vector, hVector⟩
      exact congrArg Subtype.val hAction
    · exact mul_zero element
    · intro left right hLeft hRight
      rw [mul_add, hLeft, hRight, add_zero]
  simpa using hAnnihilates 1

theorem irreducible_actions_detect_eq {G : Type} [Group G] [Fintype G]
    (left right : MonoidAlgebra ℂ G)
    (hEqual : ∀ (space : Type) [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
      (representation : Representation ℂ G space) [representation.IsIrreducible],
      representation.asAlgebraHom left = representation.asAlgebraHom right) : left = right := by
  apply sub_eq_zero.mp
  apply irreducible_actions_detect_zero
  intro space hAdd hModule hFinite representation hIrr
  rw [map_sub, hEqual space representation, sub_self]

@[expose] noncomputable def setIdempotent {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hFinite : characters.Finite) : MonoidAlgebra ℂ G :=
  ∑ character ∈ hFinite.toFinset, characterIdempotent character

theorem setIdempotent_coeff {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hFinite : characters.Finite) (element : G) :
    (setIdempotent characters hFinite).coeff element =
      BlocksIdempotentCoeff G characters element := by
  classical
  unfold setIdempotent BlocksIdempotentCoeff
  rw [finsum_mem_eq_finite_toFinset_sum _ hFinite, MonoidAlgebra.coeff_sum]
  simp [characterIdempotent, Finsupp.finsetSum_apply]

theorem representation_setIdempotent {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hFinite : characters.Finite)
    (hSubset : characters ⊆ BlocksIrr G)
    {space : Type} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) [representation.IsIrreducible] :
    representation.asAlgebraHom (setIdempotent characters hFinite) =
      if representation.character ∈ characters then LinearMap.id else 0 := by
  classical
  unfold setIdempotent
  rw [map_sum]
  have hSummands : ∀ character ∈ hFinite.toFinset,
      representation.asAlgebraHom (characterIdempotent character) =
        if representation.character = character then LinearMap.id else 0 := by
    intro character hCharacter
    exact representation_characterIdempotent representation
      (hSubset (hFinite.mem_toFinset.mp hCharacter))
  rw [Finset.sum_congr rfl hSummands]
  simp only [Finset.sum_ite_eq, Set.Finite.mem_toFinset]

theorem setIdempotent_all {G : Type} [Group G] [Fintype G] :
    setIdempotent (BlocksIrr G) (irreducibles_finite G) = 1 := by
  apply irreducible_actions_detect_eq
  intro space hAdd hModule hFinite representation hIrr
  rw [representation_setIdempotent _ _ (Set.Subset.refl _) representation, map_one]
  have hMember : representation.character ∈ BlocksIrr G :=
    ⟨space, hAdd, hModule, hFinite, representation, hIrr, rfl⟩
  simp [hMember, ← Module.End.one_eq_id]

theorem setIdempotent_inter {G : Type} [Group G] [Fintype G]
    (left right : Set (G → ℂ)) (hLeftFinite : left.Finite) (hRightFinite : right.Finite)
    (hLeftSubset : left ⊆ BlocksIrr G) (hRightSubset : right ⊆ BlocksIrr G) :
    setIdempotent (left ∩ right) (hLeftFinite.inter_of_left _) =
      setIdempotent left hLeftFinite * setIdempotent right hRightFinite := by
  apply irreducible_actions_detect_eq
  intro space hAdd hModule hFinite representation hIrr
  rw [representation_setIdempotent _ _
    (fun _ hMember => hLeftSubset hMember.1) representation, map_mul,
    representation_setIdempotent _ _ hLeftSubset representation,
    representation_setIdempotent _ _ hRightSubset representation]
  split_ifs <;> simp_all [← Module.End.one_eq_id]

theorem setIdempotent_diff {G : Type} [Group G] [Fintype G]
    (left right : Set (G → ℂ)) (hLeftFinite : left.Finite) (hRightFinite : right.Finite)
    (hLeftSubset : left ⊆ BlocksIrr G) (hRightSubset : right ⊆ left) :
    setIdempotent (left \ right) hLeftFinite.sdiff =
      setIdempotent left hLeftFinite - setIdempotent right hRightFinite := by
  apply irreducible_actions_detect_eq
  intro space hAdd hModule hFinite representation hIrr
  rw [representation_setIdempotent _ _
    (fun _ hMember => hLeftSubset hMember.1) representation, map_sub,
    representation_setIdempotent _ _ hLeftSubset representation,
    representation_setIdempotent _ _ (hRightSubset.trans hLeftSubset) representation]
  have hImplication : representation.character ∈ right → representation.character ∈ left :=
    fun hMember => hRightSubset hMember
  split_ifs <;> simp_all [← Module.End.one_eq_id]

theorem setIdempotent_isIdempotent {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hFinite : characters.Finite)
    (hSubset : characters ⊆ BlocksIrr G) :
    setIdempotent characters hFinite * setIdempotent characters hFinite =
      setIdempotent characters hFinite := by
  have hInter := setIdempotent_inter characters characters hFinite hFinite hSubset hSubset
  simpa only [Set.inter_self] using hInter.symm

theorem setIdempotent_isCentral {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hFinite : characters.Finite)
    (hSubset : characters ⊆ BlocksIrr G) (element : MonoidAlgebra ℂ G) :
    setIdempotent characters hFinite * element = element * setIdempotent characters hFinite := by
  apply irreducible_actions_detect_eq
  intro space hAdd hModule hFinite representation hIrr
  rw [map_mul, map_mul, representation_setIdempotent _ _ hSubset representation]
  split_ifs <;> simp [← Module.End.one_eq_id]

end CFSG.BlockSectionOrthogonality.Helpers
