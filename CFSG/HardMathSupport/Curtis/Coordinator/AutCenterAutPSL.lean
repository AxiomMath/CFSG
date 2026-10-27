module

public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem not_nine_dvd_four_pow_sub_one {e : ℕ} (he : ¬ 3 ∣ e) : ¬ 9 ∣ 4 ^ e - 1 := by
  have h1 : 4 ^ e % 9 = 4 ^ (e % 3) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod e 3, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hr : e % 3 = 1 ∨ e % 3 = 2 := by omega
  have hpos : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by norm_num)
  intro h
  have h2 : 4 ^ e % 9 = 1 := by omega
  rcases hr with hr | hr <;> rw [hr] at h1 <;> omega

theorem not_pow_three_dvd_eight_pow_sub_one {e : ℕ} (he : ¬ 3 ∣ e) : ¬ 27 ∣ 8 ^ e - 1 := by
  have h1 : 8 ^ e % 27 = 8 ^ (e % 6) % 27 := by
    conv_lhs => rw [← Nat.div_add_mod e 6, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hr : e % 6 = 1 ∨ e % 6 = 2 ∨ e % 6 = 4 ∨ e % 6 = 5 := by omega
  have hpos : 1 ≤ 8 ^ e := Nat.one_le_pow _ _ (by norm_num)
  intro h
  have h2 : 8 ^ e % 27 = 1 := by omega
  rcases hr with hr | hr | hr | hr <;> rw [hr] at h1 <;> omega

theorem not_pow_four_dvd_card_mulAut_psl_three {e : ℕ} (he : 1 ≤ e) (h3 : ¬ 3 ∣ e) :
    ¬ 3 ^ 4 ∣ Nat.card (MulAut (projectiveSL 3 (GaloisField 2 e))) := by
  have : NeZero e := ⟨by omega⟩
  set K := GaloisField 2 e with hKdef
  have hK : Nat.card K = 2 ^ e := GaloisField.card 2 e (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := inferInstance
  have : Finite (MulAut (projectiveSL 3 K)) :=
    Finite.of_injective (fun a : MulAut (projectiveSL 3 K) => (a : projectiveSL 3 K →
      projectiveSL 3 K)) fun a b hab => MulEquiv.ext (congrFun hab)
  set P := projectiveSL 3 K with hP
  set q := 2 ^ e with hq
  obtain ⟨-, hSL, -, -, -, -, -, -, -⟩ := linear_order 2 q hK (n := 3) (by norm_num)
  have hscal : Nat.card (scalars 3 K) = Nat.gcd 3 (q - 1) := by
    rw [card_scalars_eq_gcd K (by norm_num), hK]
  have hdvd : Nat.card (scalars 3 K) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) :=
    Subgroup.card_subgroup_dvd_card _
  have hPcard : Nat.card P * Nat.card (scalars 3 K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [hP, card_projectiveSL 3]
    exact Nat.div_mul_cancel hdvd
  have hout : Nat.card (Outer P) ∣ 2 * e * Nat.gcd 3 (q - 1) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
      Nat.prime_two he (le_refl 3) hK
  have hinn : Nat.card (inner P) ∣ Nat.card P := Subgroup.card_range_dvd _
  have hAut : Nat.card (MulAut P) = Nat.card (Outer P) * Nat.card (inner P) :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (inner P)).trans rfl
  have hdiv : Nat.card (MulAut P) ∣ 2 * e * Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [hAut, ← hPcard, hscal]
    calc Nat.card (Outer P) * Nat.card (inner P)
        ∣ (2 * e * Nat.gcd 3 (q - 1)) * Nat.card P := mul_dvd_mul hout hinn
      _ = 2 * e * (Nat.card P * Nat.gcd 3 (q - 1)) := by ring
  have hSL' : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [hSL]
    norm_num [Finset.prod_Icc_succ_top]
  intro h4
  have h4' := h4.trans (hdiv.trans (dvd_of_eq (by rw [hSL'])))
  have hcop : Nat.Coprime (3 ^ 4) (2 * e * q ^ 3) := by
    refine Nat.Coprime.pow_left 4 ?_
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (by norm_num) ?_) ?_
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    · refine Nat.Coprime.pow_right 3 ?_
      rw [hq]
      exact Nat.Coprime.pow_right e (by norm_num)
  have h5 : 3 ^ 4 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have : 3 ^ 4 ∣ (2 * e * q ^ 3) * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
      convert h4' using 1
      ring
    exact hcop.dvd_of_dvd_mul_left this
  have hA : ¬ 9 ∣ q ^ 2 - 1 := by
    rw [hq, ← pow_mul, mul_comm, pow_mul]
    exact not_nine_dvd_four_pow_sub_one h3
  have hB : ¬ 27 ∣ q ^ 3 - 1 := by
    rw [hq, ← pow_mul, mul_comm, pow_mul]
    exact not_pow_three_dvd_eight_pow_sub_one h3
  have hq1 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hA0 : q ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hB0 : q ^ 3 - 1 ≠ 0 := by
    have : 8 ≤ q ^ 3 := by nlinarith [sq_nonneg q]
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv := padicValNat.mul hA0 hB0 (p := 3)
  have h5' : 4 ≤ padicValNat 3 ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    (padicValNat_dvd_iff_le (mul_ne_zero hA0 hB0)).1 h5
  have hA' : padicValNat 3 (q ^ 2 - 1) < 2 := by
    by_contra hc
    apply hA
    have := (padicValNat_dvd_iff_le (p := 3) hA0).2 (not_lt.1 hc)
    norm_num at this
    exact this
  have hB' : padicValNat 3 (q ^ 3 - 1) < 3 := by
    by_contra hc
    apply hB
    have := (padicValNat_dvd_iff_le (p := 3) hB0).2 (not_lt.1 hc)
    norm_num at this
    exact this
  omega

end CFSG.HardMathSupport.Curtis.Coordinator
