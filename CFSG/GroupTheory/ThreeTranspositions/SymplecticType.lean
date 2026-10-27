module

public import CFSG.Fischer.Classification.Defs
public import CFSG.Fischer.Classification.Basic.Small
public import CFSG.GroupTheory.ThreeTranspositions.Basic

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer.Classification
open CFSG.Fischer
open scoped commutatorElement

variable {X : Type} [Group X] {E : Set X}

theorem hasE9_of_affine (hP : Pair X E) {d e z : X} (hd : d ∈ E) (he : e ∈ E) (hz : z ∈ E)
    (hde : d * e ≠ e * d) (hdz : d * z ≠ z * d) (hez : e * z ≠ z * e)
    (hzl : z * (d * e * d) ≠ d * e * d * z) : HasE9 X := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  have hx3 : orderOf (d * e) = 3 := Pair.orderOf_mul_eq_three hP hd he hde
  have hy3 : orderOf (d * z) = 3 := Pair.orderOf_mul_eq_three hP hd hz hdz
  by_cases hcomm : d * e * (d * z) = d * z * (d * e)
  · refine ⟨d * e, d * z, hx3, hy3, (commute_iff_eq _ _).mpr hcomm, ?_⟩
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (d * e) ^ (k % (3 : ℤ)) = d * z :=
      (zpow_eq_zpow_emod' k hR.cube_left).symm.trans hk
    have hcast : k % (3 : ℤ) = ((k % 3).toNat : ℤ) :=
      (Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0))).symm
    have hkj : (d * e) ^ (k % 3).toNat = d * z := by
      rw [← zpow_natCast, ← hcast]
      exact hk'
    have h1 : (d * e) ^ (2 * (k % 3).toNat) * (d * z) ^ 1 = 1 := by
      rw [← hkj, pow_one, ← pow_add]
      have : 2 * (k % 3).toNat + (k % 3).toNat = 3 * (k % 3).toNat := by ring
      rw [this, pow_mul, hR.cube_left, one_pow]
    exact absurd (Pair.mod_three_eq_zero_of_affine hP hd he hz hde hdz hez hzl h1).2
      (by norm_num)
  · have hc1 : ⁅d * e, d * z⁆ ≠ 1 :=
      fun h => hcomm (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hc3 : ⁅d * e, d * z⁆ ^ 3 = 1 := hR.commutator_pow_three
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcorder : orderOf ⁅d * e, d * z⁆ = 3 := orderOf_eq_prime hc3 hc1
    refine ⟨d * e, ⁅d * e, d * z⁆, hx3, hcorder, hR.commute_commutator_left.symm, ?_⟩
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hdxd : d * (d * e) * d = (d * e)⁻¹ := Pair.conj_mul_eq_inv hP hd he
    have hdc : Commute d ⁅d * e, d * z⁆ :=
      Pair.commute_commutator_of_affine hP hd he hz hde hdz hez hzl
    have hdcd : d * ⁅d * e, d * z⁆ * d = ⁅d * e, d * z⁆ := by
      calc d * ⁅d * e, d * z⁆ * d = ⁅d * e, d * z⁆ * d * d := by rw [hdc.eq]
        _ = ⁅d * e, d * z⁆ * (d * d) := by rw [mul_assoc]
        _ = ⁅d * e, d * z⁆ * 1 := by rw [Pair.mul_self hP hd]
        _ = ⁅d * e, d * z⁆ := by rw [mul_one]
    have hdcd' : d * ⁅d * e, d * z⁆ * d = (⁅d * e, d * z⁆)⁻¹ := by
      rw [← hk]
      calc d * (d * e) ^ k * d
          = (d * (d * e) * d) ^ k := by
            have h := (conj_zpow (a := d) (b := d * e) (i := k)).symm
            simpa [Pair.inv_eq hP hd] using h
        _ = ((d * e)⁻¹) ^ k := by rw [hdxd]
        _ = ((d * e) ^ k)⁻¹ := inv_zpow (d * e) k
    have hceq : ⁅d * e, d * z⁆ = (⁅d * e, d * z⁆)⁻¹ := hdcd.symm.trans hdcd'
    have hcc : ⁅d * e, d * z⁆ * ⁅d * e, d * z⁆ = 1 := by
      nth_rewrite 2 [hceq]
      exact mul_inv_cancel ⁅d * e, d * z⁆
    have hcone : ⁅d * e, d * z⁆ = 1 := by
      have h2 : ⁅d * e, d * z⁆ ^ 2 = 1 := by rw [pow_two]; exact hcc
      have h3' : ⁅d * e, d * z⁆ ^ 3 = ⁅d * e, d * z⁆ := by rw [pow_succ, h2, one_mul]
      rw [← h3', hc3]
    exact hc1 hcone

theorem isSymplecticType_of_not_hasE9 (hP : Pair X E) (hX : ¬ HasE9 X) : IsSymplecticType E := by
  intro d hd e he z hz hde
  by_contra h
  simp only [not_or] at h
  exact hX (hasE9_of_affine hP hd he hz hde (Ne.symm h.1) (Ne.symm h.2.1) h.2.2)

end CFSG.GroupTheory.ThreeTranspositions
