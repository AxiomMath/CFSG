module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FF
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCNotSL2

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

theorem card_eq_of_isSLn_two {X : Type} [Group X] {m : ℕ} (h : IsSLn X 2 m) :
    Nat.card X = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eSL⟩⟩ := h
  let : Field K := hKfield
  have : Finite K := hKfinite
  calc Nat.card X = Nat.card ↥(CFSG.Open.StatedSL 2 K) := Nat.card_congr eSL.toEquiv
    _ = Nat.card K * (Nat.card K ^ 2 - 1) := CFSG.Open.StatedAPI.card_statedSL_two K
    _ = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by rw [hKcard]

private theorem orderOf_ne_four_of_isSLn {X : Type} [Group X] {m : ℕ} (h : IsSLn X 2 m)
    (x : X) : orderOf x ≠ 4 := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eSL⟩⟩ := h
  let : Field K := hKfield
  have : Finite K := hKfinite
  let : Fintype K := Fintype.ofFinite K
  have hKcardF : Fintype.card K = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card, hKcard]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hKcardF
  intro hx
  have h4 : 4 ∣ orderOf (eSL x) := by
    rw [eSL.orderOf_eq x, hx]
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  exact CFSG.Quasithin.H13.not_four_dvd_orderOf_ch615 h2K (eSL x) h4

private theorem two_le_of_isAlt_of_six_le_card {X : Type} [Group X] {n : ℕ}
    (h' : IsAlt X n) (hcard : 6 ≤ Nat.card X) : 2 ≤ n := by
  obtain ⟨eAlt⟩ := h'
  by_contra hlt
  have hlt' : n < 2 := Nat.lt_of_not_ge hlt
  have hle : Nat.card (Fin n) ≤ 2 := by
    have : n ≤ 2 := by omega
    simpa using this
  have hbot : alternatingGroup (Fin n) = ⊥ := alternatingGroup.eq_bot_of_card_le_two hle
  have h1 : Nat.card (alternatingGroup (Fin n)) = 1 := by
    rw [hbot, Subgroup.card_bot]
  have hX1 : Nat.card X = 1 := (Nat.card_congr eAlt.toEquiv).trans h1
  omega

private theorem eq_two_and_eq_five_of_card_eq {m n : ℕ} (hm : 1 ≤ m) (hn2 : 2 ≤ n) (hn5 : n ≤ 5)
    (hcard : 2 ^ m * ((2 ^ m) ^ 2 - 1) = n.factorial / 2) : m = 2 ∧ n = 5 := by
  have hq2 : 2 ≤ 2 ^ m := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
  have hfac : n.factorial ≤ 120 := by
    calc n.factorial ≤ Nat.factorial 5 := Nat.factorial_le hn5
      _ = 120 := by norm_num
  have hdiv : n.factorial / 2 ≤ 60 := by omega
  have hLHS_le : 2 ^ m * ((2 ^ m) ^ 2 - 1) ≤ 60 := hcard.le.trans hdiv
  have h1 : 1 ≤ (2 ^ m) ^ 2 - 1 := by
    have h4 : 4 ≤ (2 ^ m) ^ 2 := by
      simpa using Nat.pow_le_pow_left hq2 2
    omega
  have hq_le : 2 ^ m ≤ 60 := by
    calc 2 ^ m = 2 ^ m * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul_left _ h1
      _ ≤ 60 := hLHS_le
  have hmle : m ≤ 5 := by
    have hlt : 2 ^ m < 2 ^ 6 := by
      calc 2 ^ m ≤ 60 := hq_le
        _ < 64 := by norm_num
        _ = 2 ^ 6 := by norm_num
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hlt
    omega
  interval_cases n <;> interval_cases m <;> norm_num at hcard
  all_goals norm_num

theorem eq_two_and_eq_five_of_isSLn_of_isAlt {X : Type} [Group X] {m n : ℕ} (hm : 1 ≤ m)
    (h : IsSLn X 2 m) (h' : IsAlt X n) : m = 2 ∧ n = 5 := by
  classical
  have hcardX := card_eq_of_isSLn_two h
  have hq2 : 2 ≤ 2 ^ m := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
  have h3 : 3 ≤ (2 ^ m) ^ 2 - 1 := by
    have h4 : 4 ≤ (2 ^ m) ^ 2 := by
      simpa using Nat.pow_le_pow_left hq2 2
    omega
  have hcardX_ge : 6 ≤ Nat.card X := by
    rw [hcardX]
    calc 6 = 2 * 3 := by norm_num
      _ ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul hq2 h3
  have hn2 := two_le_of_isAlt_of_six_le_card h' hcardX_ge
  obtain ⟨eAlt⟩ := h'
  by_cases hn : 6 ≤ n
  · obtain ⟨g, hg⟩ :=
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.exists_orderOf_eq_four_alternatingGroup hn
    have hx : orderOf (eAlt.symm g) = 4 := by
      rw [← eAlt.orderOf_eq (eAlt.symm g), eAlt.apply_symm_apply g, hg]
    exact absurd hx (orderOf_ne_four_of_isSLn h (eAlt.symm g))
  · have hn5 : n ≤ 5 := by
      have := Nat.lt_of_not_ge hn
      omega
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
    have hcardAlt : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
    have hEq : 2 ^ m * ((2 ^ m) ^ 2 - 1) = n.factorial / 2 := by
      calc 2 ^ m * ((2 ^ m) ^ 2 - 1) = Nat.card X := hcardX.symm
        _ = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr eAlt.toEquiv
        _ = n.factorial / 2 := hcardAlt
    exact eq_two_and_eq_five_of_card_eq hm hn2 hn5 hEq

end CFSG.GroupTheory
