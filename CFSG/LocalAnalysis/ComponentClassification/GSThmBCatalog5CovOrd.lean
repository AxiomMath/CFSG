module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Fus

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup

theorem one_le_pow_sub_one {q i : ℕ} (hq : 2 ≤ q) (hi : 1 ≤ i) : 1 ≤ q ^ i - 1 := by
  have : 2 ≤ q ^ i := le_trans hq (Nat.le_self_pow (by omega) q)
  omega

theorem lt_ordA_three {N q : ℕ} (hq : 2 ≤ q) (hN : 4 * (N + 1) ≤ q ^ 6) : N < Open.ordA 3 q := by
  unfold Open.ordA
  refine lt_div_of_mul_succ_le (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (Nat.gcd_le_left _ (by norm_num)) ?_
  have hP : 1 ≤ ∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - 1) :=
    Finset.one_le_prod fun i hi => one_le_pow_sub_one hq (le_trans (by norm_num)
      (Finset.mem_Icc.mp hi).1)
  calc (3 + 1) * (N + 1) ≤ q ^ (3 * (3 + 1) / 2) := hN
    _ ≤ q ^ (3 * (3 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - 1) :=
      Nat.le_mul_of_pos_right _ hP

theorem lt_ordTwistedA_three {N q : ℕ} (hq : 2 ≤ q) (hN : 4 * (N + 1) ≤ q ^ 6) :
    N < Open.ordTwistedA 3 q := by
  unfold Open.ordTwistedA
  refine lt_div_of_mul_succ_le (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (Nat.gcd_le_left _ (by norm_num)) ?_
  have hP : 1 ≤ ∏ i ∈ Finset.Icc 2 (3 + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    refine Finset.one_le_prod fun i hi => ?_
    have hi1 : 1 ≤ i := le_trans (by norm_num) (Finset.mem_Icc.mp hi).1
    have h2 : (2 : ℤ) ≤ (q : ℤ) ^ i := by
      have : 2 ≤ q ^ i := le_trans hq (Nat.le_self_pow (by omega) q)
      exact_mod_cast this
    have h1 : (-1 : ℤ) ^ i ≤ 1 := by
      rcases neg_one_pow_eq_or ℤ i with h | h
      · rw [h]
      · rw [h]; norm_num
    omega
  calc (3 + 1) * (N + 1) ≤ q ^ (3 * (3 + 1) / 2) := hN
    _ ≤ q ^ (3 * (3 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (3 + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat :=
      Nat.le_mul_of_pos_right _ hP

theorem lt_ordBC_two {N q : ℕ} (hq : 2 ≤ q) (hN : 2 * (N + 1) ≤ q ^ 4) : N < Open.ordBC 2 q := by
  unfold Open.ordBC
  refine lt_div_of_mul_succ_le (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (Nat.gcd_le_left _ (by norm_num)) ?_
  have hP : 1 ≤ ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) :=
    Finset.one_le_prod fun i hi => one_le_pow_sub_one hq (by
      have := (Finset.mem_Icc.mp hi).1
      omega)
  calc 2 * (N + 1) ≤ q ^ (2 * 2) := hN
    _ ≤ q ^ (2 * 2) * ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) := Nat.le_mul_of_pos_right _ hP

theorem lt_ordTwistedD_four {N q : ℕ} (hq : 2 ≤ q) (hN : 4 * (N + 1) ≤ q ^ 12) :
    N < Open.ordTwistedD 4 q := by
  unfold Open.ordTwistedD
  refine lt_div_of_mul_succ_le (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (Nat.gcd_le_left _ (by norm_num)) ?_
  have hP : 1 ≤ ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) :=
    Finset.one_le_prod fun i hi => one_le_pow_sub_one hq (by
      have := (Finset.mem_Icc.mp hi).1
      omega)
  calc 4 * (N + 1) ≤ q ^ (4 * (4 - 1)) := hN
    _ ≤ q ^ (4 * (4 - 1)) * (q ^ 4 + 1) := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ q ^ (4 * (4 - 1)) * (q ^ 4 + 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) :=
      Nat.le_mul_of_pos_right _ hP

theorem ne_of_lt_of_small {F : ℕ → ℕ} {N q₀ : ℕ} (hbig : ∀ q, q₀ ≤ q → N < F q)
    (hsmall : ∀ q < q₀, F q ≠ N) (q : ℕ) : F q ≠ N := by
  rcases Nat.lt_or_ge q q₀ with h | h
  · exact hsmall q h
  · exact (hbig q h).ne'

theorem card_of_cf23Exception {N J : Type} [Group N] [Group J] (h : CF23Exception N J) :
    (∃ k, (k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) ∧
        Nonempty (N ≃* alternatingGroup (Fin k))) ∨
      ∃ q, 3 ≤ q ∧ (Nat.card N = Open.ordA 3 q ∨ Nat.card N = Open.ordTwistedA 3 q ∨
        Nat.card N = Open.ordTwistedD 4 q ∨ Nat.card N = Open.ordBC 2 q ∨
        Nat.card N = Open.ordA 1 q) := by
  rcases h with ⟨n, hn, -, hN⟩ | ⟨p, f, hp, hp2, hf, -, hN⟩ | ⟨p, f, hp, hp2, hf, -, -, hN⟩
  · left
    rcases hN with hN | hN
    · refine ⟨n + 2, ?_, hN⟩
      omega
    · refine ⟨n + 4, ?_, hN⟩
      omega
  · right
    have h3 := three_le_pow_of_odd_prime hp hp2 hf
    have hc := fun {t : Assembly.LowTwoRank.StatedLieTag} {m e : ℕ} (hm : m ≠ 0)
        (h : Blueprint.LieModel N t m p e) =>
      ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (statedClassicalModel_of_lieModel_ne_zero hm h)
    rcases hN with hN | hN | ⟨e, he, hN⟩ | hN
    · exact ⟨p ^ f, h3, Or.inl ((hc (by norm_num) hN).1 rfl)⟩
    · exact ⟨p ^ f, h3, Or.inr (Or.inl ((hc (by norm_num) hN).2.1 rfl))⟩
    · refine ⟨p ^ e, three_le_pow_of_odd_prime hp hp2 (by omega), Or.inr (Or.inr (Or.inl ?_))⟩
      exact (hc (by norm_num) hN).2.2.2.2.2 rfl
    · exact ⟨p ^ f, h3, Or.inr (Or.inr (Or.inr (Or.inl ((hc (by norm_num) hN).2.2.1 rfl))))⟩
  · right
    refine ⟨p ^ (2 * f), three_le_pow_of_odd_prime hp hp2 (by omega), Or.inr (Or.inr (Or.inr
      (Or.inr ?_)))⟩
    exact (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hN)).1 rfl

theorem not_cf23Exception_of_card {S J : Type} [Group S] [Group J] {N : ℕ} (hS : Nat.card S = N)
    (hA : ∀ k, (k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) → k.factorial / 2 ≠ N)
    (h1 : ∀ q, Open.ordA 1 q ≠ N)
    (hL : ∀ q < 24, Open.ordA 3 q ≠ N) (hU : ∀ q < 24, Open.ordTwistedA 3 q ≠ N)
    (hD : ∀ q < 5, Open.ordTwistedD 4 q ≠ N) (hB : ∀ q < 98, Open.ordBC 2 q ≠ N)
    (hN : 4 * (N + 1) ≤ 5 ^ 12 ∧ 4 * (N + 1) ≤ 24 ^ 6 ∧ 2 * (N + 1) ≤ 98 ^ 4) :
    ¬ CF23Exception S J := by
  intro hE
  rcases card_of_cf23Exception hE with ⟨k, hk, ⟨e⟩⟩ | ⟨q, hq, hc⟩
  · apply hA k hk
    rw [← hS, Nat.card_congr e.toEquiv]
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  · have hq2 : 2 ≤ q := by omega
    rw [hS] at hc
    rcases hc with hc | hc | hc | hc | hc
    · exact ne_of_lt_of_small (fun q' hq' => lt_ordA_three (by omega)
        (hN.2.1.trans (Nat.pow_le_pow_left hq' 6))) hL q hc.symm
    · exact ne_of_lt_of_small (fun q' hq' => lt_ordTwistedA_three (by omega)
        (hN.2.1.trans (Nat.pow_le_pow_left hq' 6))) hU q hc.symm
    · refine ne_of_lt_of_small (q₀ := 5) (fun q' hq' => lt_ordTwistedD_four (by omega)
        (hN.1.trans ?_)) hD q hc.symm
      exact Nat.pow_le_pow_left hq' 12
    · exact ne_of_lt_of_small (fun q' hq' => lt_ordBC_two (by omega)
        (hN.2.2.trans (Nat.pow_le_pow_left hq' 4))) hB q hc.symm
    · exact h1 q hc.symm

end CFSG.ComponentClassification.GSThmB.Cov
