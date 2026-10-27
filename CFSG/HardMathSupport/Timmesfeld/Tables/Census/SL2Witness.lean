module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcUntwisted

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.LieType.Chevalley Matrix

theorem threeTwoWitness_of_injective_sl2_odd {K : Type} [Field K] (hK : ringChar K ≠ 2)
    {X : Type} [Group X] (φ : SL2 K →* X) (hφ : Function.Injective φ) : ThreeTwoWitness X := by
  refine ThreeTwoWitness.of_commuting (g := φ (HSL (-1))) (x := φ cThree) ?_ ?_ ?_ ?_
  · rw [← map_pow, pow_two, HSL_neg_one_sq, map_one]
  · intro h
    have := hφ (h.trans (map_one φ).symm)
    have h00 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) this
    simp [coe_HSL] at h00
    exact hK (neg_one_eq_one_iff.1 (by simpa using h00))
  · refine orderOf_eq_prime (by rw [← map_pow, cThree_pow_three, map_one]) ?_
    intro h
    have := hφ (h.trans (map_one φ).symm)
    have h00 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) this
    simp [coe_cThree] at h00
  · exact (Commute.map (show Commute (HSL (-1) : SL2 K) cThree from cThree_comm_HSL.symm) φ)

section Even

variable {K : Type} [Field K]

theorem uSL_mul_uSL (a b : K) : (uSL a : SL2 K) * uSL b = uSL (a + b) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [SpecialLinearGroup.coe_mul, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uSL_zero : (uSL (0 : K) : SL2 K) = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]

theorem HSL_mul_uSL (t : Kˣ) (s : K) :
    (HSL t : SL2 K) * uSL s = uSL ((t : K) ^ 2 * s) * HSL t := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [SpecialLinearGroup.coe_mul, coe_uSL, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]
  have h0 : (t : K) ≠ 0 := t.ne_zero
  field_simp

theorem HSL_pow_three {t : Kˣ} (ht : t ^ 3 = 1) : (HSL t : SL2 K) ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  have h : (t : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  have h' : ((t⁻¹ : Kˣ) : K) = (t : K) ^ 2 := by
    have : (t⁻¹ : Kˣ) = t ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', ht]
    rw [this, Units.val_pow_eq_pow_val]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [SpecialLinearGroup.coe_mul, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two, h'] <;>
    first | linear_combination h | linear_combination ((t : K) ^ 3 + 1) * h |
      linear_combination (-1 : K) * h | linear_combination (-(t : K) ^ 3) * h

end Even

theorem threeTwoWitness_of_injective_sl2_even {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : Even f) {X : Type} [Group X] [Finite X] (φ : SL2 K →* X)
    (hφ : Function.Injective φ) : ThreeTwoWitness X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (1 : K) + 1 = 0 := by
    have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
    simpa [one_add_one_eq_two] using this
  obtain ⟨m, hm⟩ := hf
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK,
      show f = 2 * m by omega, pow_mul]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 m
    rw [one_pow] at this
    exact this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hz3 : (g : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hz1 : (g : K) ≠ 1 := by
    intro h
    have : g = 1 := Units.ext (by simpa using h)
    rw [this, orderOf_one] at hg
    norm_num at hg
  have hz : (g : K) ^ 2 + (g : K) + 1 = 0 := by
    have h : ((g : K) - 1) * ((g : K) ^ 2 + (g : K) + 1) = 0 := by linear_combination hz3
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hz1)
  have hq : (g : K) ^ 2 = 1 + g := by linear_combination hz - ((g : K) + 1) * h2
  have hu1 : (uSL 1 : SL2 K) * uSL 1 = 1 := by rw [uSL_mul_uSL, h2, uSL_zero]
  have h2' : ∀ x : K, x + x = 0 := fun x => by linear_combination x * h2
  have hu2 : (uSL (g : K) : SL2 K) * uSL (g : K) = 1 := by rw [uSL_mul_uSL, h2', uSL_zero]
  have hu12 : (uSL 1 : SL2 K) * uSL (g : K) = uSL (g : K) * uSL 1 := by
    rw [uSL_mul_uSL, uSL_mul_uSL, add_comm]
  have hginv : ((g ^ 2)⁻¹ : Kˣ) = g := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, hg3]
  have hconj : ∀ s : K, (HSL (g ^ 2) : SL2 K) * uSL s * (HSL (g ^ 2))⁻¹ = uSL ((g : K) * s) := by
    intro s
    rw [mul_inv_eq_iff_eq_mul, HSL_mul_uSL]
    congr 2
    rw [Units.val_pow_eq_pow_val]
    linear_combination (g : K) * s * hz3
  have hc3 : (HSL (g ^ 2) : SL2 K) ^ 3 = 1 :=
    HSL_pow_three (by rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hg3, one_pow])
  have hcne : (HSL (g ^ 2) : SL2 K) ≠ 1 := by
    intro h
    have h00 := congrArg (fun x : SL2 K => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [coe_HSL] at h00
    rcases h00 with h | h
    · exact hz1 (by rw [h, Units.val_one])
    · exact hz1 (by rw [h, Units.val_neg, Units.val_one]; linear_combination (-1 : K) * h2)
  refine ThreeTwoWitness.of_klein (φ (uSL 1)) (φ (uSL (g : K))) (φ (HSL (g ^ 2))) ?_ ?_ ?_ ?_ ?_ ?_
    ?_
  · rw [← map_mul, hu1, map_one]
  · rw [← map_mul, hu2, map_one]
  · rw [← map_mul, ← map_mul, hu12]
  · intro h
    have := hφ (h.trans (map_one φ).symm)
    have h01 := congrArg (fun x : SL2 K => (x : Matrix (Fin 2) (Fin 2) K) 0 1) this
    simp [coe_uSL] at h01
  · exact orderOf_eq_prime (by rw [← map_pow, hc3, map_one]) fun h =>
      hcne (hφ (h.trans (map_one φ).symm))
  · rw [← map_inv, ← map_mul, ← map_mul, hconj, mul_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hconj, ← map_mul, uSL_mul_uSL]
    congr 2
    linear_combination hq

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
