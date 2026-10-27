module

public import CFSG.GF2Type.Smith1979.W4AsE11Layer
public import CFSG.GF2Type.Smith1979.W4AsSurvNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module
open scoped MatrixGroups

namespace Surv

theorem exists_root_gf8 : ∃ s : GaloisField 2 3, s ^ 3 + s + 1 = 0 := by
  set F := GaloisField 2 3
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hcard : Nat.card F = 8 := by simpa using GaloisField.card 2 3 (by norm_num)
  have h7 : 7 ∣ Nat.card Fˣ := by rw [Nat.card_units, hcard]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hg7 : (g : F) ^ 7 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hg1 : (g : F) ≠ 1 := by
    intro h
    rw [Units.val_eq_one.mp h, orderOf_one] at hg
    omega
  have hprod : ((g : F) - 1) * ((g : F) ^ 3 + g + 1) * ((g : F) ^ 3 + g ^ 2 + 1) = 0 := by
    linear_combination hg7 + ((g : F) ^ 4 - (g : F) ^ 3) * h2
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hg1
    · exact ⟨g, h⟩
  · exact ⟨(g : F) ^ 3, by linear_combination h + (g : F) ^ 2 * hg7⟩

theorem cube_eq_one_aux {F : Type*} [Field F] [CharP F 2] {s : F} (hs : s ^ 3 + s + 1 = 0) :
    (!![s, 1 + s ^ 2; 1 + s ^ 2, s + 1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (3 * s ^ 2 + s + 4) * hs + (-s ^ 2 - s - 2) * h2
  · linear_combination (s ^ 3 + 5 * s + 2) * hs + (s ^ 2 - 2 * s) * h2
  · linear_combination (s ^ 3 + 5 * s + 2) * hs + (s ^ 2 - 2 * s) * h2
  · linear_combination (3 * s ^ 2 + 2 * s + 4) * hs + (s ^ 2 - 1) * h2

theorem exists_orderOf_nine_sl2 {F : Type*} [Field F] [CharP F 2] {s : F}
    (hs : s ^ 3 + s + 1 = 0) : ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, orderOf x = 9 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let M : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, s]
  have hdet : M.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * h2
  let x : Matrix.SpecialLinearGroup (Fin 2) F := ⟨M, hdet⟩
  have hM3 : M ^ 3 = !![s, 1 + s ^ 2; 1 + s ^ 2, s + 1] := by
    rw [pow_succ, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | linear_combination hs - h2
  have hx9 : x ^ 9 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    show M ^ 9 = 1
    rw [show 9 = 3 * 3 from rfl, pow_mul, hM3]
    exact cube_eq_one_aux hs
  have hx3 : x ^ 3 ≠ 1 := by
    intro h
    have h' : M ^ 3 = 1 := by
      have := congrArg Subtype.val h
      rwa [Matrix.SpecialLinearGroup.coe_pow] at this
    rw [hM3] at h'
    have h01 := congrFun (congrFun h' 0) 1
    simp at h01
    have h3 : (s + 1) ^ 2 = 0 := by linear_combination h01 + s * h2
    have h4 : s + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h3
    have h5 : (1 : F) = 0 := by linear_combination (s ^ 2 - s + 2) * h4 - hs
    exact one_ne_zero h5
  have h9 := orderOf_eq_prime_pow (p := 3) (n := 1) (by simpa using hx3) (by simpa using hx9)
  exact ⟨x, by simpa using h9⟩

theorem exists_orderOf_nine_of_psl28 {K : Type} [Group K] [Finite K]
    (e : K ⧸ center K ≃* PSL(2, GaloisField 2 3)) : ∃ y : K, orderOf y = 9 := by
  obtain ⟨s, hs⟩ := exists_root_gf8
  obtain ⟨x, hx⟩ := exists_orderOf_nine_sl2 (F := GaloisField 2 3) hs
  set g : K ⧸ center K :=
    e.symm ((CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 3)).symm x) with hg
  have hg9 : orderOf g = 9 := by
    rw [hg, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hx]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective g
  have hdvd : 9 ∣ orderOf k := by
    rw [← hg9, ← hk]
    exact orderOf_map_dvd (QuotientGroup.mk' (center K)) k
  exact ⟨k ^ (orderOf k / 9), orderOf_pow_orderOf_div (orderOf_pos k).ne' hdvd⟩

end Surv

theorem l28NoSmallFaithful_holds : L28NoSmallFaithful := by
  intro K _ _ ⟨e⟩ V _ _ _ ρ hρ
  obtain ⟨y, hy⟩ := Surv.exists_orderOf_nine_of_psl28 e
  exact Surv.six_le_finrank_of_orderOf_eq_nine (σ := ρ y) (by rw [orderOf_injective ρ hρ, hy])

end CFSG.GF2Type.Smith1979.W4As
