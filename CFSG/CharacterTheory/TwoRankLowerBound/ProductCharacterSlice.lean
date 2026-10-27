module

public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualCharacters

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

def secondFactorRepresentation {left right vector : Type*} [Group left] [Group right]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ (left × right) vector) :
    Representation ℂ right vector := representation.comp (MonoidHom.inr left right)

theorem first_factor_preserves_second_invariants {left right vector : Type*} [Group left] [Group right]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ (left × right) vector)
    (element : left) (vectorValue : (secondFactorRepresentation representation).invariants) :
    representation (element, 1) vectorValue ∈ (secondFactorRepresentation representation).invariants := by
  apply ((secondFactorRepresentation representation).mem_invariants _).mpr
  intro member
  change representation (1, member) (representation (element, 1) (vectorValue : vector)) =
    representation (element, 1) (vectorValue : vector)
  have hcommute : representation (1, member) * representation (element, 1) =
      representation (element, 1) * representation (1, member) := by
    rw [← map_mul, ← map_mul]
    simp only [Prod.mul_def, one_mul, mul_one]
  rw [← Module.End.mul_apply, hcommute, Module.End.mul_apply]
  have hfixed := ((secondFactorRepresentation representation).mem_invariants _).mp vectorValue.property member
  exact congrArg (representation (element, 1)) hfixed

noncomputable def productFixedRepresentation {left right vector : Type*} [Group left] [Group right]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ (left × right) vector) :
    Representation ℂ left (secondFactorRepresentation representation).invariants where
  toFun element :=
    ((representation (element, 1)).comp (secondFactorRepresentation representation).invariants.subtype).codRestrict
      (secondFactorRepresentation representation).invariants
      (first_factor_preserves_second_invariants representation element)
  map_one' := by
    apply LinearMap.ext
    intro vectorValue
    apply Subtype.ext
    exact congrArg (fun operator : Module.End ℂ vector => operator vectorValue) representation.map_one
  map_mul' := by
    intro first second
    apply LinearMap.ext
    intro vectorValue
    apply Subtype.ext
    change representation (first * second, 1) (vectorValue : vector) =
      representation (first, 1) (representation (second, 1) (vectorValue : vector))
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [Prod.mul_def, one_mul]

noncomputable def secondFactorAverage {left right vector : Type*} [Group left] [Group right] [Fintype right]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ (left × right) vector) :
    Module.End ℂ vector := (Nat.card right : ℂ)⁻¹ • ∑ member : right, representation (1, member)

theorem secondFactorAverage_mem {left right vector : Type*} [Group left] [Group right] [Fintype right]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ (left × right) vector)
    (vectorValue : vector) : secondFactorAverage representation vectorValue ∈
      (secondFactorRepresentation representation).invariants := by
  apply ((secondFactorRepresentation representation).mem_invariants _).mpr
  intro element
  change representation (1, element) (secondFactorAverage representation vectorValue) = _
  simp only [secondFactorAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft element)
  intro member
  rw [← Module.End.mul_apply, ← map_mul]
  simp only [Prod.mul_def, one_mul]
  rfl

theorem secondFactorAverage_fixed {left right vector : Type*} [Group left] [Group right] [Fintype right]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ (left × right) vector)
    (vectorValue : (secondFactorRepresentation representation).invariants) :
    secondFactorAverage representation vectorValue = (vectorValue : vector) := by
  have hterm : ∀ member : right, representation (1, member) (vectorValue : vector) = vectorValue :=
    ((secondFactorRepresentation representation).mem_invariants _).mp vectorValue.property
  simp only [secondFactorAverage, LinearMap.smul_apply, LinearMap.sum_apply, hterm,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]

theorem productFixedRepresentation_character {left right vector : Type*} [Group left] [Group right]
    [Fintype right] [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ (left × right) vector) (element : left) :
    (productFixedRepresentation representation).character element =
      (Nat.card right : ℂ)⁻¹ * ∑ member : right, representation.character (element, member) := by
  let fixed := (secondFactorRepresentation representation).invariants
  let inclusion := fixed.subtype
  let projection : vector →ₗ[ℂ] fixed := (secondFactorAverage representation).codRestrict fixed
    (secondFactorAverage_mem representation)
  have hfixedOperator : (projection ∘ₗ representation (element, 1)) ∘ₗ inclusion =
      productFixedRepresentation representation element := by
    apply LinearMap.ext
    intro vectorValue
    apply Subtype.ext
    change secondFactorAverage representation (representation (element, 1) (vectorValue : vector)) = _
    exact secondFactorAverage_fixed representation
      ⟨representation (element, 1) vectorValue,
        first_factor_preserves_second_invariants representation element vectorValue⟩
  have htrace := LinearMap.trace_comp_comm' (projection ∘ₗ representation (element, 1)) inclusion
  rw [hfixedOperator] at htrace
  have hwholeOperator : inclusion ∘ₗ (projection ∘ₗ representation (element, 1)) =
      secondFactorAverage representation * representation (element, 1) := by
    ext vectorValue
    rfl
  rw [hwholeOperator] at htrace
  change LinearMap.trace ℂ fixed (productFixedRepresentation representation element) = _
  rw [← htrace, secondFactorAverage, smul_mul_assoc, Finset.sum_mul, map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro member _
  rw [← map_mul]
  simp only [Prod.mul_def, one_mul, mul_one]
  rfl

noncomputable def principalProductSlice {left right : Type*} [Group left] [Group right] [Fintype right]
    (function : left × right → ℂ) : left → ℂ :=
  fun element => (Nat.card right : ℂ)⁻¹ * ∑ member : right, function (element, member)

noncomputable def principalProductSliceLinearMap {left right : Type*} [Group left] [Group right] [Fintype right] :
    (left × right → ℂ) →ₗ[ℤ] (left → ℂ) where
  toFun := principalProductSlice
  map_add' := by
    intro first second
    ext element
    simp only [principalProductSlice, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro integer function
    ext element
    simp only [principalProductSlice, Pi.smul_apply, zsmul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

theorem principalProductSlice_virtual {left right : Type} [Group left] [Group right] [Fintype right]
    (function : left × right → ℂ) (hvirtual : function ∈ virtualCharacters (left × right)) :
    principalProductSlice function ∈ virtualCharacters left := by
  have hmap : virtualCharacters (left × right) ≤
      (virtualCharacters left).comap principalProductSliceLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨data, rfl⟩
    have hcharacter : principalProductSlice data.character =
        (productFixedRepresentation data.representation).character :=
      funext (fun element => (productFixedRepresentation_character data.representation element).symm)
    change principalProductSlice data.character ∈ virtualCharacters left
    rw [hcharacter]
    exact character_mem_virtualCharacters
      { vector := (secondFactorRepresentation data.representation).invariants,
        representation := productFixedRepresentation data.representation }
  exact hmap hvirtual

@[expose] noncomputable def productCharacterSlice {left right : Type*} [Group left] [Group right] [Fintype right]
    (character : right → ℂ) (function : left × right → ℂ) : left → ℂ :=
  fun element => (Nat.card right : ℂ)⁻¹ * ∑ member : right, function (element, member) * character member⁻¹

@[expose] noncomputable def productCharacterSliceLinearMap {left right : Type*}
    [Group left] [Group right] [Fintype right] (character : right → ℂ) :
    (left × right → ℂ) →ₗ[ℤ] (left → ℂ) where
  toFun := productCharacterSlice character
  map_add' := by
    intro first second
    ext element
    simp only [productCharacterSlice, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro integer function
    ext element
    simp only [productCharacterSlice, Pi.smul_apply, zsmul_eq_mul, RingHom.id_apply, mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem productCharacterSlice_character {left right : Type*} [Group left] [Group right] [Fintype right]
    (data : FiniteComplexRepresentation (left × right)) (other : FiniteComplexRepresentation right) :
    productCharacterSlice other.character data.character =
      (productFixedRepresentation
        (Representation.linHom (other.representation.comp (MonoidHom.snd left right)) data.representation)).character := by
  ext element
  rw [productFixedRepresentation_character]
  simp only [productCharacterSlice, Representation.char_linHom]
  congr 1
  apply Finset.sum_congr rfl
  intro member _
  change data.character (element, member) * other.character member⁻¹ =
    other.character member⁻¹ * data.character (element, member)
  ring

theorem productCharacterSlice_virtual {left right : Type} [Group left] [Group right] [Fintype right]
    (function : left × right → ℂ) (hvirtual : function ∈ virtualCharacters (left × right))
    (other : FiniteComplexRepresentation.{0, 0} right) :
    productCharacterSlice other.character function ∈ virtualCharacters left := by
  have hmap : virtualCharacters (left × right) ≤
      (virtualCharacters left).comap (productCharacterSliceLinearMap other.character) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨data, rfl⟩
    change productCharacterSlice other.character data.character ∈ virtualCharacters left
    rw [productCharacterSlice_character]
    exact character_mem_virtualCharacters
      { vector := (secondFactorRepresentation
          (Representation.linHom (other.representation.comp (MonoidHom.snd left right)) data.representation)).invariants,
        representation := productFixedRepresentation
          (Representation.linHom (other.representation.comp (MonoidHom.snd left right)) data.representation) }
  exact hmap hvirtual

theorem productCharacterSlice_support {left right : Type*} [Group left] [Group right] [Fintype right]
    (support : Set left) (character : right → ℂ) (function : left × right → ℂ)
    (hsupport : ∀ element : left, element ∉ support → ∀ member : right, function (element, member) = 0)
    (element : left) (hnot : element ∉ support) : productCharacterSlice character function element = 0 := by
  simp only [productCharacterSlice, hsupport element hnot, zero_mul, Finset.sum_const_zero, mul_zero]

theorem productCharacterSlice_parity {left right : Type*} [Group left] [Group right] [Fintype right]
    (involution : left) (parity : ℂ) (character : right → ℂ) (function : left × right → ℂ)
    (hparity : ∀ element : left, ∀ member : right,
      function (element * involution, member) = parity * function (element, member)) (element : left) :
    productCharacterSlice character function (element * involution) =
      parity * productCharacterSlice character function element := by
  simp only [productCharacterSlice, hparity, mul_assoc]
  rw [← Finset.mul_sum]
  ring

end CFSG.TwoRankLowerBound.Helpers
