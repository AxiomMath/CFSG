module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem toNat_pow_sub_neg_one_pow {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = if Even i then q ^ i - 1 else q ^ i + 1 := by
  rcases Nat.even_or_odd i with hi | hi
  · rw [ite_eq_left hi, hi.neg_one_pow]
    have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
    have h2 : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [h2, Int.toNat_natCast]
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hi), hi.neg_one_pow]
    have h2 : ((q : ℤ) ^ i - -1) = ((q ^ i + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h2, Int.toNat_natCast]

private theorem lu_card_mul {X : Type} [Group X] {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) {n f : ℕ} (hadm : StatedLieAdmissible t n 3 f)
    (h : LieModel X t n 3 f) :
    Nat.card X * lieOrderDivisor t n (3 ^ f) = lieOrderNumerator t n (3 ^ f) := by
  have hc : Nat.card X = lieOrderNumerator t n (3 ^ f) / lieOrderDivisor t n (3 ^ f) := by
    rcases ht with rfl | rfl
    · obtain ⟨-, -, hn, -, -⟩ := hadm
      rw [GH74.card_of_lieModel_PSL (by omega) h, ordA, Nat.sub_add_cancel (by omega : 1 ≤ n),
        mul_comm (n - 1) n]
      rfl
    · obtain ⟨-, -, hn, -⟩ := hadm
      rw [GH74.card_of_lieModel_PSU (by omega) (by norm_num) h, ordTwistedA,
        Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n,
        Finset.prod_congr rfl fun i _ =>
          toNat_pow_sub_neg_one_pow (Nat.one_le_pow _ _ (by norm_num : (0 : ℕ) < 3)) i]
      rfl
  rw [hc, Nat.div_mul_cancel (lieOrderDivisor_dvd_numerator hadm)]

private theorem card_psu43 {X : Type} [Group X] (h : LieModel X .PSU 4 3 1) :
    Nat.card X = 3265920 := by
  have hmul := lu_card_mul (Or.inr rfl) h.admissible h
  have hnum : lieOrderNumerator .PSU 4 (3 ^ 1) = 13063680 := by decide
  have hdiv : lieOrderDivisor .PSU 4 (3 ^ 1) = 4 := by decide
  rw [hnum, hdiv] at hmul
  omega

private theorem lu_casework {X : Type} [Group X] {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) {n f : ℕ} (hadm : StatedLieAdmissible t n 3 f)
    (h : LieModel X t n 3 f) (hc : Nat.card X = 3265920) :
    t = .PSU ∧ n = 4 ∧ f = 1 := by
  have hmul := lu_card_mul ht hadm h
  rw [hc] at hmul
  have hfac := congrArg (fun m => m.factorization 3) hmul
  rw [Nat.factorization_mul (by norm_num : (3265920 : ℕ) ≠ 0) (lieOrderDivisor_ne_zero hadm),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (not_dvd_lieOrderDivisor hadm),
      add_zero, factorization_lieOrderNumerator hadm] at hfac
  have hdvd : 3 ^ (lieSylowExponent t n * f) ∣ 3265920 := hfac ▸ Nat.ordProj_dvd 3265920 3
  have hb : lieSylowExponent t n * f ≤ 6 :=
    le_of_pow_dvd_of_not_dvd hdvd (by decide)
  have hb10 : lieSylowExponent t n * f ≤ 10 := by omega
  rcases lie_casework hadm hb10 with
    ⟨ht', hn1, hn2, hf1, hf2⟩ | ⟨ht', hn1, hn2, hf1, hf2⟩ | ⟨ht', rfl, hf1, hf2⟩
  · rcases ht' with rfl | rfl
    · exfalso
      simp only [lieSylowExponent] at hb
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hmul <;> decide
    · refine ⟨rfl, ?_⟩
      simp only [lieSylowExponent] at hb
      interval_cases n <;> interval_cases f <;> norm_num at hb <;>
        first
          | exact ⟨rfl, rfl⟩
          | (exfalso; revert hmul; decide)
  · exfalso
    rcases ht with rfl | rfl <;> rcases ht' with h' | h' <;> exact absurd h' (by decide)
  · exfalso
    rcases ht with rfl | rfl
    · exact absurd rfl ht'.1
    · exact absurd rfl ht'.2.1

theorem lieModel_psl_ne_psu43 {X : Type} [Group X] {k f : ℕ}
    (hadm : StatedLieAdmissible .PSL k 3 f) (h : LieModel X .PSL k 3 f)
    (h43 : LieModel X .PSU 4 3 1) : False := by
  have hc : Nat.card X = 3265920 := card_psu43 h43
  have hcase := lu_casework (Or.inl rfl) hadm h hc
  exact absurd hcase.1 (by decide)

theorem lieModel_psu_eq_psu43 {X : Type} [Group X] {k f : ℕ}
    (hadm : StatedLieAdmissible .PSU k 3 f) (h : LieModel X .PSU k 3 f)
    (h43 : LieModel X .PSU 4 3 1) : k = 4 ∧ f = 1 := by
  have hc : Nat.card X = 3265920 := card_psu43 h43
  have hcase := lu_casework (Or.inr rfl) hadm h hc
  exact ⟨hcase.2.1, hcase.2.2⟩

end CFSG.OddStandard.HigherRank.LinUnit
