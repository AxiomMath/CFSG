module

public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualCharacters
public import CFSG.CharacterTheory.TwoRankLowerBound.QuarticCharacter

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def pairDiagonal (left right : ℂ) : Module.End ℂ (ℂ × ℂ) where
  toFun vector := (left * vector.1, right * vector.2)
  map_add' := by intros; apply Prod.ext <;> simp [mul_add]
  map_smul' := by intros; apply Prod.ext <;> simp [smul_eq_mul, mul_left_comm]

def pairOffDiagonal (left right : ℂ) : Module.End ℂ (ℂ × ℂ) where
  toFun vector := (left * vector.2, right * vector.1)
  map_add' := by intros; apply Prod.ext <;> simp [mul_add]
  map_smul' := by intros; apply Prod.ext <;> simp [smul_eq_mul, mul_left_comm]

theorem pairDiagonal_mul_pairDiagonal (first second third fourth : ℂ) :
    pairDiagonal first second * pairDiagonal third fourth =
      pairDiagonal (first * third) (second * fourth) := by
  apply LinearMap.ext
  intro vector
  apply Prod.ext <;> simp [pairDiagonal, Module.End.mul_apply, mul_assoc]

theorem pairDiagonal_mul_pairOffDiagonal (first second third fourth : ℂ) :
    pairDiagonal first second * pairOffDiagonal third fourth =
      pairOffDiagonal (first * third) (second * fourth) := by
  apply LinearMap.ext
  intro vector
  apply Prod.ext <;> simp [pairDiagonal, pairOffDiagonal, Module.End.mul_apply, mul_assoc]

theorem pairOffDiagonal_mul_pairDiagonal (first second third fourth : ℂ) :
    pairOffDiagonal first second * pairDiagonal third fourth =
      pairOffDiagonal (first * fourth) (second * third) := by
  apply LinearMap.ext
  intro vector
  apply Prod.ext <;> simp [pairDiagonal, pairOffDiagonal, Module.End.mul_apply, mul_assoc]

theorem pairOffDiagonal_mul_pairOffDiagonal (first second third fourth : ℂ) :
    pairOffDiagonal first second * pairOffDiagonal third fourth =
      pairDiagonal (first * fourth) (second * third) := by
  apply LinearMap.ext
  intro vector
  apply Prod.ext <;> simp [pairDiagonal, pairOffDiagonal, Module.End.mul_apply, mul_assoc]

theorem pairDiagonal_trace (left right : ℂ) :
    LinearMap.trace ℂ (ℂ × ℂ) (pairDiagonal left right) = left + right := by
  have hequal : pairDiagonal left right =
      (left • (1 : Module.End ℂ ℂ)).prodMap (right • (1 : Module.End ℂ ℂ)) := by
    apply LinearMap.ext
    intro vector
    rfl
  rw [hequal, LinearMap.trace_prodMap']
  simp

theorem pairOffDiagonal_trace (left right : ℂ) :
    LinearMap.trace ℂ (ℂ × ℂ) (pairOffDiagonal left right) = 0 := by
  let diagonal := pairDiagonal 1 (-1)
  have hnegative : (diagonal * pairOffDiagonal left right) * diagonal =
      -pairOffDiagonal left right := by
    apply LinearMap.ext
    intro vector
    apply Prod.ext <;> simp [diagonal, pairDiagonal, pairOffDiagonal, Module.End.mul_apply]
  have hpositive : diagonal * (diagonal * pairOffDiagonal left right) =
      pairOffDiagonal left right := by
    apply LinearMap.ext
    intro vector
    apply Prod.ext <;> simp [diagonal, pairDiagonal, pairOffDiagonal, Module.End.mul_apply]
  have htrace := LinearMap.trace_mul_comm ℂ (diagonal * pairOffDiagonal left right) diagonal
  rw [hnegative, hpositive, map_neg] at htrace
  linear_combination -htrace / 2

noncomputable def quaternionTwoDimensionalRepresentation (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    Representation ℂ (QuaternionGroup parameter) (ℂ × ℂ) where
  toFun
    | QuaternionGroup.a residue => pairDiagonal
        (quaternionQuarticChar parameter hdiv residue)
        (quaternionQuarticChar parameter hdiv (-residue))
    | QuaternionGroup.xa residue => pairOffDiagonal
        (quaternionQuarticChar parameter hdiv (-residue))
        (quaternionQuarticChar parameter hdiv residue)
  map_one' := by
    rw [QuaternionGroup.one_def]
    apply LinearMap.ext
    intro vector
    apply Prod.ext <;> simp [pairDiagonal, AddChar.map_zero_eq_one]
  map_mul' := by
    intro left right
    cases left with
    | a left =>
      cases right with
      | a right =>
        rw [QuaternionGroup.a_mul_a, pairDiagonal_mul_pairDiagonal]
        simp [AddChar.map_add_eq_mul, mul_comm]
      | xa right =>
        rw [QuaternionGroup.a_mul_xa, pairDiagonal_mul_pairOffDiagonal]
        simp [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_comm]
    | xa left =>
      cases right with
      | a right =>
        rw [QuaternionGroup.xa_mul_a, pairOffDiagonal_mul_pairDiagonal]
        simp [AddChar.map_add_eq_mul, mul_comm]
      | xa right =>
        rw [QuaternionGroup.xa_mul_xa, pairOffDiagonal_mul_pairOffDiagonal]
        simp [sub_eq_add_neg, AddChar.map_add_eq_mul, quaternionQuarticChar_parameter,
          AddChar.map_neg_eq_inv, mul_comm]

theorem quaternionTwoDimensionalRepresentation_character_a
    (parameter : ℕ) (hdiv : 4 ∣ parameter) (residue : ZMod (2 * parameter)) :
    (quaternionTwoDimensionalRepresentation parameter hdiv).character (QuaternionGroup.a residue) =
      quaternionQuarticChar parameter hdiv residue + quaternionQuarticChar parameter hdiv (-residue) :=
  pairDiagonal_trace _ _

theorem quaternionTwoDimensionalRepresentation_character_xa
    (parameter : ℕ) (hdiv : 4 ∣ parameter) (residue : ZMod (2 * parameter)) :
    (quaternionTwoDimensionalRepresentation parameter hdiv).character (QuaternionGroup.xa residue) = 0 :=
  pairOffDiagonal_trace _ _

@[expose] def quaternionCosetSign (parameter : ℕ) : QuaternionGroup parameter → ℂ
  | QuaternionGroup.a _residue => 1
  | QuaternionGroup.xa _residue => -1

@[expose] def quaternionCosetSignHom (parameter : ℕ) : QuaternionGroup parameter →* ℂ where
  toFun := quaternionCosetSign parameter
  map_one' := rfl
  map_mul' := by
    intro left right
    cases left <;> cases right <;>
      simp [quaternionCosetSign, QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
        QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]

def quaternionSignRepresentation (parameter : ℕ) : Representation ℂ (QuaternionGroup parameter) ℂ where
  toFun element := quaternionCosetSignHom parameter element • (1 : Module.End ℂ ℂ)
  map_one' := by simp
  map_mul' := by intros; simp [smul_smul, mul_comm]

theorem quaternionSignRepresentation_character (parameter : ℕ) :
    (quaternionSignRepresentation parameter).character = quaternionCosetSign parameter := by
  ext element
  change LinearMap.trace ℂ ℂ (quaternionCosetSignHom parameter element • (1 : Module.End ℂ ℂ)) = _
  simp
  rfl

@[expose] noncomputable def quaternionLocalVirtualCharacter (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    QuaternionGroup parameter → ℂ :=
  1 + (quaternionSignRepresentation parameter).character -
    (quaternionTwoDimensionalRepresentation parameter hdiv).character

theorem quaternionLocalVirtualCharacter_mem (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    quaternionLocalVirtualCharacter parameter hdiv ∈ virtualCharacters (QuaternionGroup parameter) := by
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · rw [← principalFiniteComplexRepresentation_character (QuaternionGroup parameter)]
      exact character_mem_virtualCharacters _
    · exact character_mem_virtualCharacters
        { vector := ℂ, representation := quaternionSignRepresentation parameter }
  · exact character_mem_virtualCharacters
      { vector := ℂ × ℂ, representation := quaternionTwoDimensionalRepresentation parameter hdiv }

theorem quaternionLocalVirtualCharacter_a (parameter : ℕ) (hdiv : 4 ∣ parameter)
    (residue : ZMod (2 * parameter)) :
    quaternionLocalVirtualCharacter parameter hdiv (QuaternionGroup.a residue) =
      2 - quaternionQuarticChar parameter hdiv residue - quaternionQuarticChar parameter hdiv (-residue) := by
  simp [quaternionLocalVirtualCharacter, quaternionSignRepresentation_character,
    quaternionCosetSign, quaternionTwoDimensionalRepresentation_character_a]
  ring

theorem quaternionLocalVirtualCharacter_xa (parameter : ℕ) (hdiv : 4 ∣ parameter)
    (residue : ZMod (2 * parameter)) :
    quaternionLocalVirtualCharacter parameter hdiv (QuaternionGroup.xa residue) = 0 := by
  simp [quaternionLocalVirtualCharacter, quaternionSignRepresentation_character,
    quaternionCosetSign, quaternionTwoDimensionalRepresentation_character_xa]

@[expose] def quaternionCoordinateEquiv (parameter : ℕ) :
    QuaternionGroup parameter ≃ (ZMod (2 * parameter) ⊕ ZMod (2 * parameter)) where
  toFun
    | QuaternionGroup.a residue => Sum.inl residue
    | QuaternionGroup.xa residue => Sum.inr residue
  invFun
    | Sum.inl residue => QuaternionGroup.a residue
    | Sum.inr residue => QuaternionGroup.xa residue
  left_inv := by intro element; cases element <;> rfl
  right_inv := by intro element; cases element <;> rfl

theorem sum_quaternion_coordinates {parameter : ℕ} [NeZero parameter]
    (function : QuaternionGroup parameter → ℂ) :
    ∑ element : QuaternionGroup parameter, function element =
      (∑ residue : ZMod (2 * parameter), function (QuaternionGroup.a residue)) +
      ∑ residue : ZMod (2 * parameter), function (QuaternionGroup.xa residue) := by
  trans ∑ element : ZMod (2 * parameter) ⊕ ZMod (2 * parameter),
    Sum.elim (fun residue => function (QuaternionGroup.a residue))
      (fun residue => function (QuaternionGroup.xa residue)) element
  · exact Fintype.sum_equiv (quaternionCoordinateEquiv parameter) function _ (by
      intro element; cases element <;> rfl)
  · rw [Fintype.sum_sum_type]
    rfl

theorem quaternionLocalVirtualCharacter_inv_a (parameter : ℕ) (hdiv : 4 ∣ parameter)
    (residue : ZMod (2 * parameter)) :
    quaternionLocalVirtualCharacter parameter hdiv (QuaternionGroup.a residue)⁻¹ =
      quaternionLocalVirtualCharacter parameter hdiv (QuaternionGroup.a residue) := by
  have hinverse : (QuaternionGroup.a residue)⁻¹ = QuaternionGroup.a (-residue) := by
    apply inv_eq_of_mul_eq_one_left
    simp only [QuaternionGroup.a_mul_a, neg_add_cancel, QuaternionGroup.a_zero]
  rw [hinverse, quaternionLocalVirtualCharacter_a, quaternionLocalVirtualCharacter_a, neg_neg]
  ring

theorem quaternionLocalVirtualCharacter_norm_formula
    (parameter : ℕ) [NeZero parameter] (hdiv : 4 ∣ parameter) :
    characterPairing (quaternionLocalVirtualCharacter parameter hdiv)
      (quaternionLocalVirtualCharacter parameter hdiv) =
      (Nat.card (QuaternionGroup parameter) : ℂ)⁻¹ *
        ∑ residue : ZMod (2 * parameter),
          (2 - quaternionQuarticChar parameter hdiv residue -
            quaternionQuarticChar parameter hdiv (-residue)) ^ 2 := by
  unfold characterPairing
  rw [sum_quaternion_coordinates]
  simp only [quaternionLocalVirtualCharacter_inv_a, quaternionLocalVirtualCharacter_xa,
    zero_mul, Finset.sum_const_zero, add_zero, ← pow_two, quaternionLocalVirtualCharacter_a]

theorem quaternionLocalVirtualCharacter_principal_formula
    (parameter : ℕ) [NeZero parameter] (hdiv : 4 ∣ parameter) :
    characterPairing (quaternionLocalVirtualCharacter parameter hdiv) 1 =
      (Nat.card (QuaternionGroup parameter) : ℂ)⁻¹ *
        ∑ residue : ZMod (2 * parameter),
          (2 - quaternionQuarticChar parameter hdiv residue -
            quaternionQuarticChar parameter hdiv (-residue)) := by
  unfold characterPairing
  simp only [Pi.one_apply, mul_one]
  rw [sum_quaternion_coordinates]
  simp only [quaternionLocalVirtualCharacter_xa, Finset.sum_const_zero, add_zero,
    quaternionLocalVirtualCharacter_a]

theorem quaternionLocalVirtualCharacter_principal
    (parameter : ℕ) [NeZero parameter] (hdiv : 4 ∣ parameter) :
    characterPairing (quaternionLocalVirtualCharacter parameter hdiv) 1 = 1 := by
  rw [quaternionLocalVirtualCharacter_principal_formula]
  have hneg : (∑ residue : ZMod (2 * parameter),
      quaternionQuarticChar parameter hdiv (-residue)) = 0 := by
    rw [← quaternionQuarticChar_sum parameter hdiv]
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (by intros; rfl)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    quaternionQuarticChar_sum parameter hdiv, hneg]
  simp only [sub_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ZMod.card, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hnonzero : (parameter : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne parameter)
  push_cast
  field_simp
  norm_num

theorem quaternionLocalVirtualCharacter_norm
    (parameter : ℕ) [NeZero parameter] (hdiv : 4 ∣ parameter) :
    characterPairing (quaternionLocalVirtualCharacter parameter hdiv)
      (quaternionLocalVirtualCharacter parameter hdiv) = 3 := by
  rw [quaternionLocalVirtualCharacter_norm_formula]
  have hneg : (∑ residue : ZMod (2 * parameter),
      quaternionQuarticChar parameter hdiv (-residue)) = 0 := by
    rw [← quaternionQuarticChar_sum parameter hdiv]
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (by intros; rfl)
  have hnegsquare : (∑ residue : ZMod (2 * parameter),
      quaternionQuarticChar parameter hdiv (-residue) ^ 2) = 0 := by
    rw [← quaternionQuarticChar_square_sum parameter hdiv]
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (by intros; rfl)
  have hpointwise : ∀ residue : ZMod (2 * parameter),
      (2 - quaternionQuarticChar parameter hdiv residue -
        quaternionQuarticChar parameter hdiv (-residue)) ^ 2 =
      6 - 4 * quaternionQuarticChar parameter hdiv residue -
        4 * quaternionQuarticChar parameter hdiv (-residue) +
        quaternionQuarticChar parameter hdiv residue ^ 2 +
        quaternionQuarticChar parameter hdiv (-residue) ^ 2 := by
    intro residue
    have hproduct := quaternionQuarticChar_neg_mul_self parameter hdiv residue
    linear_combination 2 * hproduct
  simp_rw [hpointwise]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    quaternionQuarticChar_sum parameter hdiv, hneg,
    quaternionQuarticChar_square_sum parameter hdiv, hnegsquare]
  simp only [mul_zero, sub_zero, add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ZMod.card, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hnonzero : (parameter : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne parameter)
  push_cast
  field_simp
  norm_num

theorem quaternionLocalVirtualCharacter_one
    (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    quaternionLocalVirtualCharacter parameter hdiv 1 = 0 := by
  rw [QuaternionGroup.one_def, quaternionLocalVirtualCharacter_a]
  norm_num [AddChar.map_zero_eq_one]

end CFSG.TwoRankLowerBound.Helpers
