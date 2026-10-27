module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionCyclicSection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def quaternionEightParityChar : AddChar (ZMod 4) ℂ := quarticAddChar + quarticAddChar

theorem quaternionEightParityChar_neg (residue : ZMod 4) :
    quaternionEightParityChar (-residue) = quaternionEightParityChar residue := by
  have hfour : quarticAddChar residue ^ 4 = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    have hzero : (4 : ℕ) • residue = 0 := by
      rw [nsmul_eq_mul]
      norm_num only [Nat.cast_ofNat]
      have hcast : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
      rw [hcast, zero_mul]
    rw [hzero, AddChar.map_zero_eq_one]
  have hnonzero : quarticAddChar residue ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by omega : 4 ≠ 0)] at hfour
    exact zero_ne_one hfour
  simp only [quaternionEightParityChar, AddChar.add_apply, AddChar.map_neg_eq_inv]
  field_simp
  linear_combination -hfour

theorem quaternionEightParityChar_two : quaternionEightParityChar 2 = 1 := by
  change (-1 : ℂ) * -1 = 1
  ring

set_option backward.isDefEq.respectTransparency false in
@[expose] def quaternionEightOtherSignHom : QuaternionGroup 2 →* ℂ where
  toFun
    | QuaternionGroup.a residue => quaternionEightParityChar residue
    | QuaternionGroup.xa residue => quaternionEightParityChar residue
  map_one' := AddChar.map_zero_eq_one _
  map_mul' := by
    intro left right
    cases left with
    | a left =>
      cases right with
      | a right =>
        rw [QuaternionGroup.a_mul_a]
        exact AddChar.map_add_eq_mul _ _ _
      | xa right =>
        rw [QuaternionGroup.a_mul_xa]
        change quaternionEightParityChar (right - left) =
          quaternionEightParityChar left * quaternionEightParityChar right
        rw [sub_eq_add_neg, AddChar.map_add_eq_mul, quaternionEightParityChar_neg, mul_comm]
    | xa left =>
      cases right with
      | a right =>
        rw [QuaternionGroup.xa_mul_a]
        exact AddChar.map_add_eq_mul _ _ _
      | xa right =>
        rw [QuaternionGroup.xa_mul_xa]
        change quaternionEightParityChar (2 + right - left) =
          quaternionEightParityChar left * quaternionEightParityChar right
        rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
          quaternionEightParityChar_neg, quaternionEightParityChar_two, one_mul, mul_comm]

@[expose] def scalarHomRepresentation {G : Type*} [Group G] (homomorphism : G →* ℂ) :
    Representation ℂ G ℂ where
  toFun element := homomorphism element • (1 : Module.End ℂ ℂ)
  map_one' := by simp
  map_mul' := by intros; simp [smul_smul, mul_comm]

theorem scalarHomRepresentation_character {G : Type*} [Group G]
    (homomorphism : G →* ℂ) :
    (scalarHomRepresentation homomorphism).character = homomorphism := by
  ext element
  change LinearMap.trace ℂ ℂ (homomorphism element • (1 : Module.End ℂ ℂ)) = _
  simp

@[expose] noncomputable def quaternionEightLocalFour : QuaternionGroup 2 → ℂ :=
  1 + (scalarHomRepresentation (quaternionCosetSignHom 2)).character -
    (scalarHomRepresentation quaternionEightOtherSignHom).character -
    (scalarHomRepresentation ((quaternionCosetSignHom 2) * quaternionEightOtherSignHom)).character

theorem quaternionEightLocalFour_mem :
    quaternionEightLocalFour ∈ virtualCharacters (QuaternionGroup 2) := by
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · apply Submodule.add_mem
      · rw [← principalFiniteComplexRepresentation_character (QuaternionGroup 2)]
        exact character_mem_virtualCharacters _
      · exact character_mem_virtualCharacters
          { vector := ℂ, representation := scalarHomRepresentation (quaternionCosetSignHom 2) }
    · exact character_mem_virtualCharacters
        { vector := ℂ, representation := scalarHomRepresentation quaternionEightOtherSignHom }
  · exact character_mem_virtualCharacters
      { vector := ℂ, representation := scalarHomRepresentation
          ((quaternionCosetSignHom 2) * quaternionEightOtherSignHom) }

theorem quaternionEightLocalFour_a (residue : ZMod 4) :
    quaternionEightLocalFour (QuaternionGroup.a residue) =
      2 - 2 * quaternionEightParityChar residue := by
  simp only [quaternionEightLocalFour, Pi.sub_apply, Pi.add_apply, Pi.one_apply,
    scalarHomRepresentation_character, MonoidHom.mul_apply]
  change 1 + 1 - quaternionEightParityChar residue - 1 * quaternionEightParityChar residue = _
  ring

theorem quaternionEightLocalFour_xa (residue : ZMod 4) :
    quaternionEightLocalFour (QuaternionGroup.xa residue) = 0 := by
  simp only [quaternionEightLocalFour, Pi.sub_apply, Pi.add_apply, Pi.one_apply,
    scalarHomRepresentation_character, MonoidHom.mul_apply]
  change 1 + -1 - quaternionEightParityChar residue - -1 * quaternionEightParityChar residue = _
  ring

theorem quaternionEightLocalFour_conjugate (element conjugator : QuaternionGroup 2) :
    quaternionEightLocalFour (conjugator * element * conjugator⁻¹) =
      quaternionEightLocalFour element := by
  simp only [quaternionEightLocalFour, Pi.sub_apply, Pi.add_apply, Pi.one_apply,
    Representation.char_conj]

set_option backward.isDefEq.respectTransparency false in
theorem quaternionEightLocalFour_principal : characterPairing quaternionEightLocalFour 1 = 1 := by
  unfold characterPairing
  rw [sum_quaternion_coordinates]
  simp only [Pi.one_apply, mul_one, quaternionEightLocalFour_xa, Finset.sum_const_zero,
    add_zero, quaternionEightLocalFour_a]
  norm_num only [QuaternionGroup.card, Nat.card_eq_fintype_card]
  change (1 / 8 : ℂ) * ∑ residue : Fin 4, (2 - 2 * quaternionEightParityChar residue) = 1
  norm_num [quaternionEightParityChar, AddChar.add_apply, quarticAddChar, quarticValue,
    ZMod.val, QuaternionGroup.card, Nat.card_eq_fintype_card, Fin.sum_univ_succ]

set_option backward.isDefEq.respectTransparency false in
theorem quaternionEightLocalFour_norm :
    characterPairing quaternionEightLocalFour quaternionEightLocalFour = 4 := by
  unfold characterPairing
  rw [sum_quaternion_coordinates]
  simp only [quaternionEightLocalFour_xa, zero_mul, Finset.sum_const_zero, add_zero,
    quaternion_a_inv, quaternionEightLocalFour_a]
  norm_num only [QuaternionGroup.card, Nat.card_eq_fintype_card]
  change (1 / 8 : ℂ) * ∑ residue : ZMod 4,
    (2 - 2 * quaternionEightParityChar residue) * (2 - 2 * quaternionEightParityChar (-residue)) = 4
  simp only [quaternionEightParityChar_neg]
  change (1 / 8 : ℂ) * ∑ residue : Fin 4,
    (2 - 2 * quaternionEightParityChar residue) * (2 - 2 * quaternionEightParityChar residue) = 4
  norm_num [quaternionEightParityChar, AddChar.add_apply, quarticAddChar, quarticValue,
    ZMod.val, QuaternionGroup.card, Nat.card_eq_fintype_card, Fin.sum_univ_succ]

set_option backward.isDefEq.respectTransparency false in
theorem quaternionEightLocalFour_root_supported (element : QuaternionGroup 2)
    (hnotroot : element ∉ cyclicRootSet (QuaternionGroup.a (1 : ZMod 4))) :
    quaternionEightLocalFour element = 0 := by
  cases element with
  | a residue =>
    fin_cases residue
    · change quaternionEightLocalFour (QuaternionGroup.a (0 : ZMod 4)) = 0
      rw [quaternionEightLocalFour_a]
      norm_num [quaternionEightParityChar, AddChar.add_apply,
        quarticAddChar, quarticValue, ZMod.val]
    · exact False.elim (hnotroot (Subgroup.mem_zpowers _))
    · norm_num [quaternionEightLocalFour_a, quaternionEightParityChar, AddChar.add_apply,
        quarticAddChar, quarticValue, ZMod.val]
    · have hroot : QuaternionGroup.a (n := 2) (1 : ZMod 4) ∈
          Subgroup.zpowers (QuaternionGroup.a (n := 2) (3 : ZMod 4)) := by
        have hinverse := quaternion_a_inv 2 (3 : ZMod 4)
        have hneg : -(3 : ZMod 4) = 1 := by decide
        rw [hneg] at hinverse
        rw [← hinverse]
        exact (Subgroup.zpowers _).inv_mem (Subgroup.mem_zpowers _)
      exact False.elim (hnotroot hroot)
  | xa residue => exact quaternionEightLocalFour_xa residue

end CFSG.TwoRankLowerBound.Helpers
