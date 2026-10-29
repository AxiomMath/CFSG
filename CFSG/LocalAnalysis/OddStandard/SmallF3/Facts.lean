module

public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.OddStandard.SmallF3

open CFSG.Blueprint CFSG.Open CFSG.OddStandard.SmallF3Interfaces

@[expose] def smallF3Orders : Finset ℕ :=
  {5616, 6048, 25920, 6065280, 3265920, 4585351680, 4952179814400, 10151968619520}

private theorem card_lieModel_PSL_3_3 {Q : Type} [Group Q] (h : LieModel Q .PSL 3 3 1) :
    Nat.card Q = 5616 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl
  rw [hc]
  decide +kernel

private theorem card_lieModel_PSU_3_3 {Q : Type} [Group Q] (h : LieModel Q .PSU 3 3 1) :
    Nat.card Q = 6048 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl
  rw [hc]
  decide +kernel

private theorem card_lieModel_PSp_2_3 {Q : Type} [Group Q] (h : LieModel Q .PSp 2 3 1) :
    Nat.card Q = 25920 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.1 rfl
  rw [hc]
  decide +kernel

private theorem card_lieModel_PSL_4_3 {Q : Type} [Group Q] (h : LieModel Q .PSL 4 3 1) :
    Nat.card Q = 6065280 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl
  rw [hc]
  decide +kernel

private theorem card_lieModel_PSU_4_3 {Q : Type} [Group Q] (h : LieModel Q .PSU 4 3 1) :
    Nat.card Q = 3265920 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl
  rw [hc]
  decide +kernel

private theorem card_lieModel_POmegaOdd_3_3 {Q : Type} [Group Q]
    (h : LieModel Q .POmegaOdd 3 3 1) : Nat.card Q = 4585351680 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.1 rfl
  rw [hc]
  decide +kernel

private theorem card_lieModel_POmegaPlus_4_3 {Q : Type} [Group Q]
    (h : LieModel Q .POmegaPlus 4 3 1) : Nat.card Q = 4952179814400 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.1 rfl
  rw [hc]
  decide +kernel

private theorem card_lieModel_POmegaMinus_4_3 {Q : Type} [Group Q]
    (h : LieModel Q .POmegaMinus 4 3 1) : Nat.card Q = 10151968619520 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.2 rfl
  rw [hc]
  decide +kernel

theorem card_mem_smallF3Orders {Q : Type} [Group Q] (hQ : SmallF3LieQuotient Q) :
    Nat.card Q ∈ smallF3Orders := by
  unfold SmallF3LieQuotient at hQ
  rcases hQ with h | h | h | h | h | h | h | h
  · rw [card_lieModel_PSL_3_3 h]; simp [smallF3Orders]
  · rw [card_lieModel_PSU_3_3 h]; simp [smallF3Orders]
  · rw [card_lieModel_PSp_2_3 h]; simp [smallF3Orders]
  · rw [card_lieModel_PSL_4_3 h]; simp [smallF3Orders]
  · rw [card_lieModel_PSU_4_3 h]; simp [smallF3Orders]
  · rw [card_lieModel_POmegaOdd_3_3 h]; simp [smallF3Orders]
  · rw [card_lieModel_POmegaPlus_4_3 h]; simp [smallF3Orders]
  · rw [card_lieModel_POmegaMinus_4_3 h]; simp [smallF3Orders]

theorem oddLieType {Q : Type} [Group Q] (hQ : SmallF3LieQuotient Q) : OddLieType Q := by
  unfold SmallF3LieQuotient at hQ
  rcases hQ with h | h | h | h | h | h | h | h
  · exact ⟨.PSL, 3, 3, 1, Nat.prime_three, by norm_num, h.admissible, h⟩
  · exact ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num, h.admissible, h⟩
  · exact ⟨.PSp, 2, 3, 1, Nat.prime_three, by norm_num, h.admissible, h⟩
  · exact ⟨.PSL, 4, 3, 1, Nat.prime_three, by norm_num, h.admissible, h⟩
  · exact ⟨.PSU, 4, 3, 1, Nat.prime_three, by norm_num, h.admissible, h⟩
  · exact ⟨.POmegaOdd, 3, 3, 1, Nat.prime_three, by norm_num, h.admissible, h⟩
  · exact ⟨.POmegaPlus, 4, 3, 1, Nat.prime_three, by norm_num, h.admissible, h⟩
  · exact ⟨.POmegaMinus, 4, 3, 1, Nat.prime_three, by norm_num, h.admissible, h⟩

private theorem nat_card_alternatingGroup_fin (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = Nat.factorial m / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem not_nonempty_mulEquiv_alternatingGroup {Q : Type} [Group Q]
    (hQ : SmallF3LieQuotient Q) (m : ℕ) : ¬ Nonempty (Q ≃* alternatingGroup (Fin m)) := by
  rintro ⟨e⟩
  have hcard : Nat.card (alternatingGroup (Fin m)) ∈ smallF3Orders := by
    rw [← Nat.card_congr e.toEquiv]
    exact card_mem_smallF3Orders hQ
  by_cases hm1 : m ≤ 1
  · haveI : Subsingleton (Fin m) :=
      Fintype.card_le_one_iff_subsingleton.mp (by simpa [Fintype.card_fin] using hm1)
    have h1 : Nat.card (alternatingGroup (Fin m)) = 1 := Nat.card_unique
    rw [h1] at hcard
    exact absurd hcard (by decide)
  · push Not at hm1
    have hm2 : 2 ≤ m := by omega
    rw [nat_card_alternatingGroup_fin m hm2] at hcard
    by_cases hm15 : m ≤ 15
    · interval_cases m <;> exact absurd hcard (by decide)
    · push Not at hm15
      have hle : Nat.factorial m / 2 ≤ 10151968619520 := by
        simp only [smallF3Orders, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
          or_false] at hcard
        omega
      have hbig : 10151968619520 < Nat.factorial m / 2 := by
        rw [Nat.lt_div_iff_mul_lt (by norm_num : (0 : ℕ) < 2)]
        have h16 : 16 ≤ m := by omega
        have hfac : Nat.factorial 16 ≤ Nat.factorial m := Nat.factorial_le h16
        have h16v : Nat.factorial 16 = 20922789888000 := by decide
        omega
      omega

theorem not_card_dvd_card_M12 {Q : Type} [Group Q] (hQ : SmallF3LieQuotient Q) :
    ¬ Nat.card Q ∣ 2 ^ 6 * 3 ^ 3 * 5 * 11 := by
  have hmem := card_mem_smallF3Orders hQ
  simp only [smallF3Orders, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h <;>
    rw [h, Nat.dvd_iff_mod_eq_zero] <;> decide +kernel

theorem not_statedClassicalModel_psl_two_eight {Q : Type} [Group Q]
    (hQ : SmallF3LieQuotient Q) :
    ¬ Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 2 3 := by
  intro h
  have h504 : Nat.card Q = 504 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight h
  have hmem := card_mem_smallF3Orders hQ
  rw [h504] at hmem
  exact absurd hmem (by decide)

end CFSG.OddStandard.SmallF3
