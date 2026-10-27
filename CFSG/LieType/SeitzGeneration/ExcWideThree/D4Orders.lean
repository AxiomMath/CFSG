module

public import CFSG.HardMathSupport.Lang.Triality.WeylCert
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Timmesfeld.Orders.ExceptionalTorus

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.HardMathSupport.Lang.Triality

section Orders

@[expose] def d4Chain : List (ChainStep Tag.D4) :=
  [⟨15, 0, d4FullCert, [(2, 1), (4, 1), (4, 1), (6, 1)]⟩]

theorem d4Chain_check : chainCheck d4Chain 15 = true := by
  decide +kernel

theorem sum_length_D4 [Fintype (WeylGroup .D4)] (q : ℕ) :
    ∑ w : WeylGroup .D4, q ^ (coxeterSystem .D4).length w =
      geomSum 2 1 q * geomSum 4 1 q * geomSum 4 1 q * geomSum 6 1 q := by
  rw [← parabolicSum_univ, ← maskSet_full (m := 15) (by decide),
    parabolicSum_eq_of_chainCheck q _ _ d4Chain_check]
  simp only [d4Chain, ChainStep.value, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil]
  ring

theorem ncard_posRoots_D4 :
    {α : Fin Tag.D4.rank → ℤ | IsRoot .D4 α ∧ 0 < height α}.ncard = 12 :=
  (ncard_setOf_isRoot_and fun α => 0 < height α).trans (by decide +kernel)

theorem geomSum_one_dvd_pow_sub_one (n q : ℕ) (hq : 1 ≤ q) : geomSum n 1 q ∣ q ^ n - 1 := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ hq
  have h : ((geomSum n 1 q : ℕ) : ℤ) * ((q : ℤ) - 1) = (q : ℤ) ^ n - 1 := by
    have := geom_sum_mul (q : ℤ) n
    simpa [geomSum] using this
  refine Int.natCast_dvd_natCast.1 ?_
  rw [Nat.cast_sub h1]
  exact ⟨(q : ℤ) - 1, by simpa using h.symm⟩

variable {K : Type} [Field K] [Finite K]


theorem card_adjointGroup_D4_eq :
    Nat.card (adjointGroup Tag.D4 K) = Nat.card (torusGroup Tag.D4 K) * Nat.card K ^ 12 *
      (geomSum 2 1 (Nat.card K) * geomSum 4 1 (Nat.card K) * geomSum 4 1 (Nat.card K) *
        geomSum 6 1 (Nat.card K)) := by
  classical
  have : Fintype (WeylGroup .D4) := Fintype.ofFinite _
  rw [card_adjointGroup, finsum_eq_sum_of_fintype, sum_length_D4, ncard_posRoots_D4]

theorem not_dvd_card_adjointGroup_D4 {r : ℕ} (hr : r.Prime) (hq : ¬ r ∣ Nat.card K)
    (hj : ∀ j, 0 < j → j < 12 → ¬ r ∣ Nat.card K ^ j - 1) :
    ¬ r ∣ Nat.card (adjointGroup Tag.D4 K) := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hH : Nat.card (torusGroup Tag.D4 K) ∣ (Nat.card K - 1) ^ 4 :=
    Dvd.intro _ (card_torusGroup_mul (τ := Tag.D4) (K := K))
  rw [card_adjointGroup_D4_eq]
  intro h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hj 1 (by norm_num) (by norm_num) (by
        simpa using hr.dvd_of_dvd_pow (h.trans hH))
    · exact hq (hr.dvd_of_dvd_pow h)
  · have h2 := geomSum_one_dvd_pow_sub_one 2 (Nat.card K) hq1
    have h4 := geomSum_one_dvd_pow_sub_one 4 (Nat.card K) hq1
    have h6 := geomSum_one_dvd_pow_sub_one 6 (Nat.card K) hq1
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact hj 2 (by norm_num) (by norm_num) (h.trans h2)
        · exact hj 4 (by norm_num) (by norm_num) (h.trans h4)
      · exact hj 4 (by norm_num) (by norm_num) (h.trans h4)
    · exact hj 6 (by norm_num) (by norm_num) (h.trans h6)

end Orders

section Zsigmondy


theorem exists_primitive_prime_pow_twelve (q : ℕ) (hq : 2 ≤ q) :
    ∃ r : ℕ, r.Prime ∧ r ∣ q ^ 12 - 1 ∧ ∀ k, 0 < k → k < 12 → ¬ r ∣ q ^ k - 1 := by
  by_cases h2 : q = 2
  · subst h2
    exact CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one 12 (by norm_num)
      (by norm_num)
  · exact CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (by omega)
      (by norm_num)

theorem exists_prime_dvd_pow_eight_add_not_dvd_card_D4 {K : Type} [Field K] [Finite K]
    (hK : 2 ≤ Nat.card K) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card K ^ 8 + Nat.card K ^ 4 + 1 ∧
      ¬ r ∣ Nat.card (adjointGroup Tag.D4 K) := by
  obtain ⟨r, hr, hr12, hrk⟩ := exists_primitive_prime_pow_twelve (Nat.card K) hK
  refine ⟨r, hr, ?_, not_dvd_card_adjointGroup_D4 hr ?_ hrk⟩
  · have h4 := hrk 4 (by norm_num) (by norm_num)
    have hfac : Nat.card K ^ 12 - 1 =
        (Nat.card K ^ 4 - 1) * (Nat.card K ^ 8 + Nat.card K ^ 4 + 1) := by
      have h1 : 1 ≤ Nat.card K ^ 4 := Nat.one_le_pow _ _ (by omega)
      zify [h1, show 1 ≤ Nat.card K ^ 12 from Nat.one_le_pow _ _ (by omega)]
      ring
    rw [hfac] at hr12
    exact ((Nat.Prime.dvd_mul hr).1 hr12).resolve_left h4
  · intro hrq
    have h1 : r ∣ Nat.card K ^ 12 := dvd_pow hrq (by norm_num)
    have h2 : r ∣ 1 := by
      have h3 : 1 ≤ Nat.card K ^ 12 := Nat.one_le_pow _ _ (by omega)
      have h4 := Nat.dvd_sub h1 hr12
      rwa [Nat.sub_sub_self h3] at h4
    exact hr.one_lt.ne' (Nat.dvd_one.1 h2)

end Zsigmondy

end CFSG.LieType.SeitzGeneration.ExcWideThree
