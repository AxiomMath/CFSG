module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLFlagEmbed

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj StatedSU)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.LieType.BorelTits (unitaryForm statedSU_preserves)

namespace OLPSUFour

theorem natCard_gl_fin {F : Type*} [Field F] [Finite F] (a : ℕ) :
    Nat.card (GL (Fin a) F) = ∏ i : Fin a, (Nat.card F ^ a - Nat.card F ^ (i : ℕ)) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Nat.card_eq_fintype_card (α := F)]

theorem padicValNat_three_two_pow_sub_one {m : ℕ} (h : m % 6 = 2 ∨ m % 6 = 4) :
    padicValNat 3 (2 ^ m - 1) = 1 :=
  OLThreeAdic.padicValNat_three_sub_one_one Nat.one_le_two_pow (OLThreeAdic.two_pow_mod_nine_even h)

theorem padicValNat_three_card_gl_zero {F : Type*} [Field F] [Finite F] :
    padicValNat 3 (Nat.card (GL (Fin 0) F)) = 0 := by
  rw [natCard_gl_fin]
  simp

theorem padicValNat_three_card_gl_one {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hm : m % 6 = 2 ∨ m % 6 = 4) (hX : Nat.card F = 2 ^ m) :
    padicValNat 3 (Nat.card (GL (Fin 1) F)) = 1 := by
  rw [natCard_gl_fin, hX]
  simpa using padicValNat_three_two_pow_sub_one hm

theorem padicValNat_three_card_gl_two {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hm : m % 6 = 2 ∨ m % 6 = 4) (hX : Nat.card F = 2 ^ m) :
    padicValNat 3 (Nat.card (GL (Fin 2) F)) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm2 : 2 ≤ 2 ^ m := calc
    2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfac : Nat.card (GL (Fin 2) F) = ((2 ^ m) ^ 2 - 1) * (2 ^ m * (2 ^ m - 1)) := by
    rw [natCard_gl_fin, Fin.prod_univ_two, hX, Nat.mul_sub_one]
    simp [sq]
  have h1 : padicValNat 3 ((2 ^ m) ^ 2 - 1) = 1 := by
    rw [← pow_mul]
    exact padicValNat_three_two_pow_sub_one (by omega)
  have h2 : padicValNat 3 (2 ^ m - 1) = 1 := padicValNat_three_two_pow_sub_one hm
  have hne1 : (2 ^ m) ^ 2 - 1 ≠ 0 := by
    have : 2 ≤ (2 ^ m) ^ 2 := le_trans hm2 (Nat.le_self_pow (by norm_num) _)
    omega
  have hne2 : 2 ^ m - 1 ≠ 0 := by omega
  have hne3 : 2 ^ m * (2 ^ m - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hne2
  rw [hfac, padicValNat.mul hne1 hne3, padicValNat.mul (pow_ne_zero _ two_ne_zero) hne2, h1, h2,
    padicValNat.eq_zero_of_not_dvd (OLThreeAdic.not_three_dvd_two_pow m)]

theorem four_le_padicValNat_numerator_PSU_four :
    4 ≤ padicValNat 3 (lieOrderNumerator .PSU 4 (2 ^ 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : lieOrderNumerator .PSU 4 (2 ^ 1) = 2 ^ 6 * (3 * 9 * 15) := by decide
  have hne : lieOrderNumerator .PSU 4 (2 ^ 1) ≠ 0 := by rw [h]; norm_num
  exact (padicValNat_dvd_iff_le hne).mp (by rw [h]; norm_num)

end OLPSUFour

theorem twoLocalWhen_PSU_four : TwoLocalWhen .PSU (fun n f₀ => n = 4 ∧ f₀ = 1) := by
  intro K _ _ hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  obtain ⟨rfl, rfl⟩ := hP
  have hcl0 : StatedClassicalModel K .PSU 4 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hfp : f = p := by rw [hf, mul_one]
  have hp6 := OLThreeAdic.prime_mod_six hp hp5
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨e⟩⟩ := hcl0
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hFcard, ← pow_mul, mul_comm]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  have hX : Nat.card F = 2 ^ (2 * p) := by rw [hFcard, ← pow_mul, mul_comm, hfp]
  have hm : (2 * p) % 6 = 2 ∨ (2 * p) % 6 = 4 := by omega
  have hGL0 := OLPSUFour.padicValNat_three_card_gl_zero (F := F)
  have hGL1 := OLPSUFour.padicValNat_three_card_gl_one hm hX
  have hGL2 := OLPSUFour.padicValNat_three_card_gl_two hm hX
  refine ⟨3, Nat.prime_three, fun R hR2 hR1 => ?_⟩
  have hB : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ Fintype.card (Fin 4) →
      padicValNat 3 (Nat.card (GL (Fin k) F)) +
        padicValNat 3 (Nat.card (GL (Fin (Fintype.card (Fin 4) - 2 * k)) F)) ≤ 3 := by
    intro k hk1 hk2
    rw [Fintype.card_fin] at hk2 ⊢
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl
    · show padicValNat 3 (Nat.card (GL (Fin 1) F)) + padicValNat 3 (Nat.card (GL (Fin 2) F)) ≤ 3
      omega
    · show padicValNat 3 (Nat.card (GL (Fin 2) F)) + padicValNat 3 (Nat.card (GL (Fin 0) F)) ≤ 3
      omega
  have hle := OLFlag.padicValNat_three_card_normalizer_le_of_isometries_of_equiv e
    (unitaryForm 2 f hFcard 4) (fun A hA u v => statedSU_preserves hFcard hA u v) 3 hB R hR2 hR1
  have hd : lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by decide
  have h4 := OLPSUFour.four_le_padicValNat_numerator_PSU_four
  rw [hd, padicValNat.one]
  omega

theorem overgroupLocalWhen_PSU_four (hOver : CFSG.Quasithin.AsLieTwoOvergroups) :
    OvergroupLocalWhen .PSU (fun n f₀ => n = 4 ∧ f₀ = 1) :=
  overgroupLocalWhen_of_twoLocalWhen hOver twoLocalWhen_PSU_four

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
