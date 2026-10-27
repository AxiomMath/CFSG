module

public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.Open.StatedDefs
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.Final.ModelOrd

theorem odd_card_subgroupOf_scalars {K : Type} [Field K] [Finite K] {q d : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : Even q) (hq0 : q ≠ 0) (H : Subgroup (GL (Fin d) K)) :
    Odd (Nat.card ((StatedScalars (Fin d) K).subgroupOf H)) := by
  by_contra hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ((StatedScalars (Fin d) K).subgroupOf H) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 x.2
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hm : x ^ (q ^ 2 - 1) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have hc1 : c ^ (q ^ 2 - 1) = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have : ((x : H) : GL (Fin d) K) ^ (q ^ 2 - 1) = 1 := by
      rw [← hc, ← map_pow, hc1, map_one]
    simpa using this
  have hdvd : orderOf x ∣ q ^ 2 - 1 := orderOf_dvd_of_pow_eq_one hm
  rw [hx] at hdvd
  have hqq : Even (q ^ 2) := hq.pow_of_ne_zero (by norm_num)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)
  obtain ⟨r, hr⟩ := hqq
  omega

theorem padicValNat_card_statedSU {K : Type} [Field K] [Finite K] {a d : ℕ} (ha : 1 ≤ a) (hd : 1 ≤ d)
    (hK : Nat.card K = (2 ^ a) ^ 2) :
    padicValNat 2 (Nat.card (StatedSU d (2 ^ a) K)) = a * (d * (d - 1) / 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata : UnitaryFieldData 2 a K := ⟨Nat.prime_two, ha, by rw [hK, ← pow_mul, Nat.mul_comm]⟩
  have h := card_statedSU_int hdata hd
  set N := d * (d - 1) / 2 with hN
  set P : ℤ := ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) with hP
  have hPodd : Odd P := by
    refine Finset.prod_induction _ Odd (fun x y hx hy => hx.mul hy) odd_one ?_
    intro i hi
    have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.1 hi).1; omega
    have hev : Even (((2 ^ a : ℕ) : ℤ) ^ i) := by
      have : Even ((2 ^ a : ℕ) : ℤ) := by
        have h2 : (2 : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) := by
          push_cast
          exact dvd_pow_self 2 (by omega)
        exact even_iff_two_dvd.2 h2
      exact this.pow_of_ne_zero (by omega)
    have hodd : Odd ((-1 : ℤ) ^ i) := by
      rcases neg_one_pow_eq_or ℤ i with h1 | h1 <;> rw [h1]
      · exact odd_one
      · exact ⟨-1, by norm_num⟩
    exact hev.sub_odd hodd
  have hHpos : 0 < Nat.card (StatedSU d (2 ^ a) K) := Nat.card_pos
  have hPpos : 0 < P := by
    by_contra hneg
    push Not at hneg
    have h1 : (0 : ℤ) < ((2 ^ a : ℕ) : ℤ) ^ N := by positivity
    have h2 : (0 : ℤ) < (Nat.card (StatedSU d (2 ^ a) K) : ℤ) := by exact_mod_cast hHpos
    rw [h] at h2
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = P := ⟨P.toNat, Int.toNat_of_nonneg hPpos.le⟩
  have hmodd : Odd m := by
    have : Odd (m : ℤ) := hm ▸ hPodd
    exact (Int.odd_coe_nat m).1 this
  have hcard : Nat.card (StatedSU d (2 ^ a) K) = (2 ^ a) ^ N * m := by
    have : (Nat.card (StatedSU d (2 ^ a) K) : ℤ) = (((2 ^ a) ^ N * m : ℕ) : ℤ) := by
      rw [h, ← hm]
      push_cast
      rfl
    exact_mod_cast this
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hmodd
  have hv : padicValNat 2 m = 0 :=
    padicValNat.eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hmodd.not_two_dvd_nat)
  rw [hcard, padicValNat.mul (pow_ne_zero _ (pow_ne_zero _ (by norm_num))) hm0, ← pow_mul,
    padicValNat.prime_pow, hv, add_zero]

theorem padicValNat_card_psu {K : Type} [Field K] [Finite K] {a d : ℕ} (ha : 1 ≤ a) (hd : 1 ≤ d)
    (hK : Nat.card K = (2 ^ a) ^ 2) :
    padicValNat 2 (Nat.card (StatedProj (StatedSU d (2 ^ a) K))) = a * (d * (d - 1) / 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin d) K).subgroupOf (StatedSU d (2 ^ a) K))
  have hodd := odd_card_subgroupOf_scalars hK (q := 2 ^ a) (d := d)
    (Even.pow_of_ne_zero (by norm_num) (by omega)) (pow_ne_zero _ (by norm_num)) (StatedSU d (2 ^ a) K)
  have hpos1 : 0 < Nat.card (StatedProj (StatedSU d (2 ^ a) K)) := Nat.card_pos
  have hpos2 : 0 < Nat.card ((StatedScalars (Fin d) K).subgroupOf (StatedSU d (2 ^ a) K)) := Nat.card_pos
  have hv : padicValNat 2 (Nat.card ((StatedScalars (Fin d) K).subgroupOf (StatedSU d (2 ^ a) K))) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hodd.not_two_dvd_nat)
  have := padicValNat_card_statedSU ha hd hK
  rw [h1, padicValNat.mul hpos1.ne' hpos2.ne', hv, add_zero] at this
  exact this

theorem eq_of_mul_eq_twenty {a d : ℕ} (hd : 5 ≤ d) (ha : 1 ≤ a) (h : a * (d * (d - 1) / 2) = 20) :
    d = 5 ∧ a = 2 := by
  have hd7 : d < 7 := by
    by_contra hd7
    push Not at hd7
    have h1 : 21 ≤ d * (d - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have : 42 ≤ d * (d - 1) := by
        have h2 : 6 ≤ d - 1 := by omega
        nlinarith
      omega
    nlinarith
  interval_cases d
  · omega
  · omega

end CFSG.LieType.SemisimpleCentralizers.HeldLang
