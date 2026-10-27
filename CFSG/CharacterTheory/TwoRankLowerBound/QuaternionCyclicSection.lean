module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionCharacters
public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicRootLayers

public section

open scoped Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

def quaternionCyclicHom (parameter : ℕ) :
    Multiplicative (ZMod (2 * parameter)) →* QuaternionGroup parameter where
  toFun residue := QuaternionGroup.a residue.toAdd
  map_one' := rfl
  map_mul' := fun left right => (QuaternionGroup.a_mul_a left.toAdd right.toAdd).symm

theorem quaternionCyclicHom_injective (parameter : ℕ) :
    Function.Injective (quaternionCyclicHom parameter) := by
  intro left right hequal
  exact QuaternionGroup.a.inj hequal

theorem quaternion_a_zpow (parameter : ℕ) (residue : ZMod (2 * parameter))
    (exponent : ℤ) : QuaternionGroup.a residue ^ exponent =
      QuaternionGroup.a (exponent • residue) := by
  exact (map_zpow (quaternionCyclicHom parameter) (Multiplicative.ofAdd residue) exponent).symm

theorem quaternion_a_inv (parameter : ℕ) (residue : ZMod (2 * parameter)) :
    (QuaternionGroup.a residue)⁻¹ = QuaternionGroup.a (-residue) := by
  apply inv_eq_of_mul_eq_one_right
  rw [QuaternionGroup.a_mul_a, add_neg_cancel]
  rfl

theorem quaternion_xa_inv (parameter : ℕ) (residue : ZMod (2 * parameter)) :
    (QuaternionGroup.xa residue)⁻¹ = QuaternionGroup.xa ((parameter : ZMod (2 * parameter)) + residue) := by
  apply inv_eq_of_mul_eq_one_right
  rw [QuaternionGroup.xa_mul_xa]
  have hzero : (parameter : ZMod (2 * parameter)) + (parameter : ZMod (2 * parameter)) = 0 := by
    rw [← Nat.cast_add]
    convert ZMod.natCast_self (2 * parameter) using 1
    congr 1
    omega
  have heq : (parameter : ZMod (2 * parameter)) +
      ((parameter : ZMod (2 * parameter)) + residue) - residue = 0 := by
    rw [← add_assoc, hzero, zero_add, sub_self]
  rw [heq]
  rfl

theorem quaternion_a_conjugate (parameter : ℕ) (residue : ZMod (2 * parameter))
    (conjugator : QuaternionGroup parameter) :
    conjugator * QuaternionGroup.a residue * conjugator⁻¹ =
      QuaternionGroup.a residue ∨
    conjugator * QuaternionGroup.a residue * conjugator⁻¹ =
      (QuaternionGroup.a residue)⁻¹ := by
  cases conjugator with
  | a coordinate =>
    left
    rw [quaternion_a_inv, QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a]
    congr 1
    abel
  | xa coordinate =>
    right
    rw [quaternion_xa_inv, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa,
      quaternion_a_inv]
    congr 1
    have hzero : (parameter : ZMod (2 * parameter)) + (parameter : ZMod (2 * parameter)) = 0 := by
      rw [← Nat.cast_add]
      convert ZMod.natCast_self (2 * parameter) using 1
      congr 1
      omega
    linear_combination hzero

theorem quaternion_a_normalizes_zpowers (parameter : ℕ)
    (residue : ZMod (2 * parameter)) (conjugator : QuaternionGroup parameter) :
    conjugator ∈ Subgroup.normalizer
      (Subgroup.zpowers (QuaternionGroup.a residue) : Set (QuaternionGroup parameter)) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  rcases quaternion_a_conjugate parameter residue conjugator with hequal | hequal
  · change Subgroup.zpowers (conjugator * QuaternionGroup.a residue * conjugator⁻¹) = _
    rw [hequal]
  · change Subgroup.zpowers (conjugator * QuaternionGroup.a residue * conjugator⁻¹) = _
    rw [hequal, Subgroup.zpowers_inv]

theorem quaternion_square_order {parameter : ℕ} [NeZero parameter] :
    orderOf ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2) = parameter := by
  rw [orderOf_pow_of_dvd (by omega : 2 ≠ 0)]
  · rw [QuaternionGroup.orderOf_a_one, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  · rw [QuaternionGroup.orderOf_a_one]
    exact dvd_mul_right 2 parameter

theorem quaternion_square_centralizer_le_cyclic {parameter : ℕ} [NeZero parameter]
    (hlarge : 2 < parameter) :
    Subgroup.centralizer
      ({(QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2} : Set (QuaternionGroup parameter)) ≤
      Subgroup.zpowers (QuaternionGroup.a (1 : ZMod (2 * parameter))) := by
  intro member hmember
  cases member with
  | a coordinate =>
    rw [← ZMod.natCast_zmod_val coordinate, ← QuaternionGroup.a_one_pow]
    exact Subgroup.npow_mem_zpowers _ _
  | xa coordinate =>
    have hcommute := (Subgroup.mem_centralizer_singleton_iff.mp hmember)
    have hconjugate : QuaternionGroup.xa coordinate *
        (QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2 *
          (QuaternionGroup.xa coordinate)⁻¹ =
        ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2)⁻¹ := by
      rw [QuaternionGroup.a_one_pow, quaternion_xa_inv, QuaternionGroup.xa_mul_a,
        QuaternionGroup.xa_mul_xa, quaternion_a_inv]
      congr 1
      have hzero : (parameter : ZMod (2 * parameter)) + (parameter : ZMod (2 * parameter)) = 0 := by
        rw [← Nat.cast_add]
        convert ZMod.natCast_self (2 * parameter) using 1
        congr 1
        omega
      linear_combination hzero
    have hequal : (QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2 =
        ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2)⁻¹ := by
      rw [← hconjugate, hcommute]
      group
    have hpow : ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2) ^ 2 = 1 := by
      rw [pow_two]
      calc
        (QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2 *
            (QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2 =
          ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2)⁻¹ *
            (QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2 :=
          congrArg (fun element => element *
            (QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2) hequal
        _ = 1 := inv_mul_cancel _
    have hdiv := orderOf_dvd_of_pow_eq_one hpow
    rw [quaternion_square_order] at hdiv
    have hle := Nat.le_of_dvd (by omega : 0 < 2) hdiv
    omega

theorem quaternion_a_mem_cyclic (parameter : ℕ) [NeZero parameter]
    (residue : ZMod (2 * parameter)) :
    QuaternionGroup.a residue ∈ Subgroup.zpowers
      (QuaternionGroup.a (1 : ZMod (2 * parameter))) := by
  rw [← ZMod.natCast_zmod_val residue, ← QuaternionGroup.a_one_pow]
  exact Subgroup.npow_mem_zpowers _ _

theorem quaternion_generator_centralizer_le_cyclic {parameter : ℕ} [NeZero parameter]
    (horder : 2 < orderOf (QuaternionGroup.a (1 : ZMod (2 * parameter)))) :
    Subgroup.centralizer
      ({QuaternionGroup.a (1 : ZMod (2 * parameter))} : Set (QuaternionGroup parameter)) ≤
      Subgroup.zpowers (QuaternionGroup.a (1 : ZMod (2 * parameter))) := by
  intro member hmember
  cases member with
  | a residue => exact quaternion_a_mem_cyclic parameter residue
  | xa residue =>
    have hcommute := Subgroup.mem_centralizer_singleton_iff.mp hmember
    have hconjugate := quaternion_a_conjugate parameter
      (1 : ZMod (2 * parameter)) (QuaternionGroup.xa residue)
    have hinversion : QuaternionGroup.xa residue * QuaternionGroup.a (1 : ZMod (2 * parameter)) *
        (QuaternionGroup.xa residue)⁻¹ = (QuaternionGroup.a (1 : ZMod (2 * parameter)))⁻¹ := by
      rw [quaternion_xa_inv, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa,
        quaternion_a_inv]
      congr 1
      have hzero : (parameter : ZMod (2 * parameter)) +
          (parameter : ZMod (2 * parameter)) = 0 := by
        rw [← Nat.cast_add]
        convert ZMod.natCast_self (2 * parameter) using 1
        congr 1
        omega
      linear_combination hzero
    have hequal : QuaternionGroup.a (1 : ZMod (2 * parameter)) =
        (QuaternionGroup.a (1 : ZMod (2 * parameter)))⁻¹ := by
      rw [← hinversion, hcommute]
      group
    have hpow : QuaternionGroup.a (1 : ZMod (2 * parameter)) ^ 2 = 1 := by
      rw [pow_two]
      calc
        QuaternionGroup.a (1 : ZMod (2 * parameter)) * QuaternionGroup.a (1 : ZMod (2 * parameter)) =
            (QuaternionGroup.a (1 : ZMod (2 * parameter)))⁻¹ *
              QuaternionGroup.a (1 : ZMod (2 * parameter)) :=
          congrArg (fun element => element * QuaternionGroup.a (1 : ZMod (2 * parameter))) hequal
        _ = 1 := inv_mul_cancel _
    have hdiv := orderOf_dvd_of_pow_eq_one hpow
    have hle := Nat.le_of_dvd (by omega : 0 < 2) hdiv
    omega

theorem quaternion_square_root_a_iff {parameter : ℕ} [NeZero parameter]
    (htwo : IsPGroup 2 (QuaternionGroup parameter)) (hlarge : 2 < parameter)
    (residue : ZMod (2 * parameter)) :
    QuaternionGroup.a residue ∈ cyclicRootSet
      ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2) ↔
      QuaternionGroup.a residue ∉ Subgroup.zpowers
        ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 4) := by
  exact cyclic_two_group_square_root_layers htwo _ _
    (by rw [QuaternionGroup.orderOf_a_one]; omega) (quaternion_a_mem_cyclic parameter residue)

theorem quaternionQuarticChar_four (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    quaternionQuarticChar parameter hdiv (4 : ZMod (2 * parameter)) = 1 := by
  have hvalue := AddChar.map_nsmul_eq_pow (quaternionQuarticChar parameter hdiv)
    4 (1 : ZMod (2 * parameter))
  norm_num [nsmul_eq_mul, quaternionQuarticChar_one, Complex.I_sq] at hvalue
  exact hvalue

theorem quaternionLocalVirtualCharacter_fourth_powers_zero (parameter : ℕ)
    (hdiv : 4 ∣ parameter) (element : QuaternionGroup parameter)
    (hmember : element ∈ Subgroup.zpowers
      ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 4)) :
    quaternionLocalVirtualCharacter parameter hdiv element = 0 := by
  obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmember
  rw [QuaternionGroup.a_one_pow, quaternion_a_zpow, quaternionLocalVirtualCharacter_a]
  norm_cast
  rw [AddChar.map_zsmul_eq_zpow, quaternionQuarticChar_four, one_zpow,
    AddChar.map_neg_eq_inv, AddChar.map_zsmul_eq_zpow, quaternionQuarticChar_four,
    one_zpow, inv_one]
  norm_num

theorem quaternionLocalVirtualCharacter_root_supported {parameter : ℕ} [NeZero parameter]
    (htwo : IsPGroup 2 (QuaternionGroup parameter)) (hlarge : 2 < parameter)
    (hdiv : 4 ∣ parameter) (element : QuaternionGroup parameter)
    (hnotroot : element ∉ cyclicRootSet
      ((QuaternionGroup.a (1 : ZMod (2 * parameter))) ^ 2)) :
    quaternionLocalVirtualCharacter parameter hdiv element = 0 := by
  cases element with
  | a residue =>
    apply quaternionLocalVirtualCharacter_fourth_powers_zero
    exact not_not.mp (fun hnot => hnotroot
      ((quaternion_square_root_a_iff htwo hlarge residue).mpr hnot))
  | xa residue => exact quaternionLocalVirtualCharacter_xa parameter hdiv residue

end CFSG.TwoRankLowerBound.Helpers
