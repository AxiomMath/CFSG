module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpValProof

theorem padicValNat_sp6_two_aux1 {N : ℕ} (hN : N % 3 = 2) :
    padicValNat 3 (N ^ 2 - 1) = padicValNat 3 (N + 1) := by
  have h3 : ¬ 3 ∣ N - 1 := by omega
  have hsq : N ^ 2 - 1 = (N + 1) * (N - 1) := by
    have h := Nat.pow_two_sub_pow_two N 1
    rwa [one_pow] at h
  rw [hsq, padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd h3, add_zero]

theorem padicValNat_sp6_two_aux2 {N : ℕ} (hN : N % 3 = 2) :
    padicValNat 3 (N ^ 4 - 1) = padicValNat 3 (N + 1) := by
  have hsq2 : N ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hN] <;> norm_num
  have hn2 : ¬ 3 ∣ N ^ 2 + 1 := by omega
  have hv0 : padicValNat 3 (N ^ 2 + 1) = 0 := padicValNat.eq_zero_of_not_dvd hn2
  have hA := padicValNat_sp6_two_aux1 hN
  have hN1 : 1 < N := by omega
  have hbig : 1 < N ^ 2 := Nat.one_lt_pow (by norm_num) hN1
  have hsq : N ^ 4 - 1 = (N ^ 2 + 1) * (N ^ 2 - 1) := by
    have h := Nat.pow_two_sub_pow_two (N ^ 2) 1
    rw [one_pow] at h
    rw [show N ^ 4 = (N ^ 2) ^ 2 by ring]
    exact h
  rw [hsq, padicValNat.mul (by omega) (by omega), hv0, hA, zero_add]

theorem padicValNat_sp6_two_aux3 {N : ℕ} (hN : N % 3 = 2) :
    padicValNat 3 (N ^ 6 - 1) = padicValNat 3 (N + 1) + 1 := by
  have hcube : N ^ 3 % 3 = 2 := by
    rw [Nat.pow_mod, hN] <;> norm_num
  have hm3 : ¬ 3 ∣ N ^ 3 - 1 := by omega
  have hlift : padicValNat 3 (N ^ 3 + 1) = padicValNat 3 (N + 1) + 1 := by
    have h := padicValNat.pow_add_pow (p := 3) (x := N) (y := 1) (n := 3) (by decide)
      (by omega) (by omega) (by decide)
    rw [one_pow, padicValNat_self] at h
    exact h
  have hsq : N ^ 6 - 1 = (N ^ 3 + 1) * (N ^ 3 - 1) := by
    have h := Nat.pow_two_sub_pow_two (N ^ 3) 1
    rw [one_pow] at h
    rw [show N ^ 6 = (N ^ 3) ^ 2 by ring]
    exact h
  rw [hsq, padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd hm3, hlift,
    add_zero]

theorem padicValNat_sp6_two {N : ℕ} (hN : N % 3 = 2) :
    padicValNat 3 (N ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (N ^ (2 * j) - 1)) =
      3 * padicValNat 3 (N + 1) + 1 := by
  have hI : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by norm_num)]
  simp only [show 2 * 1 = 2 by norm_num, show 2 * 2 = 4 by norm_num, show 2 * 3 = 6 by norm_num]
  have hN0 : N ≠ 0 := by omega
  have hN1 : 1 < N := by omega
  have h2 : N ^ 2 - 1 ≠ 0 := by
    have hb : 1 < N ^ 2 := Nat.one_lt_pow (by norm_num) hN1
    omega
  have h4 : N ^ 4 - 1 ≠ 0 := by
    have hb : 1 < N ^ 4 := Nat.one_lt_pow (by norm_num) hN1
    omega
  have h6 : N ^ 6 - 1 ≠ 0 := by
    have hb : 1 < N ^ 6 := Nat.one_lt_pow (by norm_num) hN1
    omega
  have hNp : padicValNat 3 (N ^ (3 ^ 2)) = 0 := by
    rw [padicValNat.pow N (3 ^ 2), padicValNat.eq_zero_of_not_dvd (by omega), mul_zero]
  rw [padicValNat.mul (pow_ne_zero _ hN0) (mul_ne_zero h2 (mul_ne_zero h4 h6)),
    padicValNat.mul h2 (mul_ne_zero h4 h6), padicValNat.mul h4 h6, hNp,
    padicValNat_sp6_two_aux1 hN, padicValNat_sp6_two_aux2 hN, padicValNat_sp6_two_aux3 hN]
  ring

theorem factorization_statedSp_three_of_two {F : Type} [Field F] [Finite F]
    (hN : Nat.card F % 3 = 2) :
    (Nat.card (CFSG.Open.StatedSp 3 F)).factorization 3 =
      3 * padicValNat 3 (Nat.card F + 1) + 1 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 3,
    Nat.factorization_def _ Nat.prime_three]
  exact padicValNat_sp6_two hN

end K421SpValProof

end CFSG.LocalAnalysis.RankThreeUC.S15
