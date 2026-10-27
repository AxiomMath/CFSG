module

public import CFSG.Walter.W67.Interface

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Walter.W67

universe u

theorem lcs_succ_eq_bot_of_le_center {Q : Type u} [Group Q] {n : ℕ}
    (h : (⊤ : Subgroup Q).lowerCentralSeries n ≤ Subgroup.center Q) :
    (⊤ : Subgroup Q).lowerCentralSeries (n + 1) = ⊥ := by
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  have hx' := h hx
  rw [Subgroup.mem_center_iff] at hx'
  rw [Subgroup.mem_centralizer_iff]
  intro g _
  exact (hx' g)

theorem lcs_le_of_quotient_eq_bot {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal] {n : ℕ}
    (h : (⊤ : Subgroup (Q ⧸ N)).lowerCentralSeries n = ⊥) :
    (⊤ : Subgroup Q).lowerCentralSeries n ≤ N := by
  have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup Q) (QuotientGroup.mk' N) n
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), h] at hmap
  intro g hg
  have : QuotientGroup.mk' N g ∈ (⊥ : Subgroup (Q ⧸ N)) := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hg
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact this

theorem lcs_one_eq_bot_of_comm {Q : Type u} [Group Q] (h : ∀ a b : Q, a * b = b * a) :
    (⊤ : Subgroup Q).lowerCentralSeries 1 = ⊥ := by
  rw [Subgroup.top_lowerCentralSeries_one, commutator_def,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x _
  rw [Subgroup.mem_centralizer_iff]
  intro g _
  exact h g x

theorem lcs_eq_bot_of_card {p : ℕ} [hp : Fact p.Prime] :
    ∀ k : ℕ, ∀ (Q : Type u) [Group Q] [Finite Q], IsPGroup p Q → Nat.card Q = p ^ k →
      2 ≤ k → (⊤ : Subgroup Q).lowerCentralSeries (k - 1) = ⊥ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Q _ _ hQ hk hk2
  by_cases hc : ∀ a b : Q, a * b = b * a
  · rw [eq_bot_iff]
    refine (Subgroup.lowerCentralSeries_antitone _ (Nat.le_sub_of_add_le (by omega) :
      1 ≤ k - 1)).trans ?_
    rw [lcs_one_eq_bot_of_comm hc]
  · have hnt : Nontrivial Q := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hc fun a b => Subsingleton.elim _ _
    set Z := Subgroup.center Q with hZ
    have hZnt : Nontrivial Z := hQ.center_nontrivial
    have hQZ : IsPGroup p (Q ⧸ Z) := hQ.to_quotient Z
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQZ
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hZp : IsPGroup p Z := hQ.to_subgroup Z
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp hZp
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hi
        have := Finite.one_lt_card_iff_nontrivial.mpr hZnt
        omega
      · exact h0
    have hjk : j + i = k := by
      have : p ^ k = p ^ (j + i) := by rw [← hk, hmul, hj, hi, pow_add]
      exact (Nat.pow_right_injective hp.out.two_le this).symm
    have hj2 : 2 ≤ j := by
      by_contra hlt
      apply hc
      have hcyc : IsCyclic (Q ⧸ Z) := by
        have : j ≤ 1 := by omega
        have hprime : Nat.card (Q ⧸ Z) ∣ p := by
          rw [hj]
          calc p ^ j ∣ p ^ 1 := pow_dvd_pow p this
            _ = p := pow_one p
        rcases (Nat.dvd_prime hp.out).mp hprime with h1 | h1
        · haveI : Subsingleton (Q ⧸ Z) := (Nat.card_eq_one_iff_unique.mp h1).1
          infer_instance
        · haveI : Fact (Nat.card (Q ⧸ Z)).Prime := ⟨by rw [h1]; exact hp.out⟩
          exact isCyclic_of_prime_card h1
      exact fun a b => commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z)
        (by simp [QuotientGroup.ker_mk', hZ]) a b
    have h1 := ih j (by omega) (Q ⧸ Z) hQZ hj hj2
    have h2 := lcs_le_of_quotient_eq_bot Z h1
    have h3 := lcs_succ_eq_bot_of_le_center h2
    rw [show j - 1 + 1 = j by omega] at h3
    rw [eq_bot_iff]
    exact (Subgroup.lowerCentralSeries_antitone _ (by omega : j ≤ k - 1)).trans h3.le

theorem exists_center_card_of_noncomm {p : ℕ} [hp : Fact p.Prime] {Q : Type u} [Group Q]
    [Finite Q] (hQ : IsPGroup p Q) (hc : ¬ ∀ a b : Q, a * b = b * a) :
    ∃ i j : ℕ, 1 ≤ i ∧ 2 ≤ j ∧ Nat.card (Subgroup.center Q) = p ^ i ∧
      Nat.card (Q ⧸ Subgroup.center Q) = p ^ j := by
  have hnt : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hc fun a b => Subsingleton.elim _ _
  set Z := Subgroup.center Q with hZ
  have hZnt : Nontrivial Z := hQ.center_nontrivial
  have hQZ : IsPGroup p (Q ⧸ Z) := hQ.to_quotient Z
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQZ
  have hZp : IsPGroup p Z := hQ.to_subgroup Z
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp hZp
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hi
      have := Finite.one_lt_card_iff_nontrivial.mpr hZnt
      omega
    · exact h0
  have hj2 : 2 ≤ j := by
    by_contra hlt
    apply hc
    have hcyc : IsCyclic (Q ⧸ Z) := by
      have : j ≤ 1 := by omega
      have hprime : Nat.card (Q ⧸ Z) ∣ p := by
        rw [hj]
        calc p ^ j ∣ p ^ 1 := pow_dvd_pow p this
          _ = p := pow_one p
      rcases (Nat.dvd_prime hp.out).mp hprime with h1 | h1
      · have : Subsingleton (Q ⧸ Z) := (Nat.card_eq_one_iff_unique.mp h1).1
        infer_instance
      · have : Fact (Nat.card (Q ⧸ Z)).Prime := ⟨by rw [h1]; exact hp.out⟩
        exact isCyclic_of_prime_card h1
    exact fun a b => (QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center
      (by simp [QuotientGroup.ker_mk', hZ]) |>.is_comm.comm a b
  exact ⟨i, j, hi1, hj2, hi, hj⟩

theorem card_center_of_maxClass {p : ℕ} [hp : Fact p.Prime] {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P) {m : ℕ} (hm : 3 ≤ m) (hcard : Nat.card P = p ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥) :
    Nat.card (Subgroup.center P) = p := by
  have hc : ¬ ∀ a b : P, a * b = b * a := by
    intro hc
    apply hne
    rw [eq_bot_iff]
    refine (Subgroup.lowerCentralSeries_antitone _ (by omega : 1 ≤ m - 2)).trans ?_
    rw [lcs_one_eq_bot_of_comm hc]
  obtain ⟨i, j, hi1, hj2, hi, hj⟩ := exists_center_card_of_noncomm hP hc
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
  have hij : j + i = m := by
    have : p ^ m = p ^ (j + i) := by rw [← hcard, hmul, hj, hi, pow_add]
    exact (Nat.pow_right_injective hp.out.two_le this).symm
  by_contra hne1
  have hi2 : 2 ≤ i := by
    by_contra h
    apply hne1
    rw [hi]
    have : i = 1 := by omega
    rw [this, pow_one]
  have h1 := lcs_eq_bot_of_card j (P ⧸ Subgroup.center P) (hP.to_quotient _) hj hj2
  have h2 := lcs_le_of_quotient_eq_bot _ h1
  have h3 := lcs_succ_eq_bot_of_le_center h2
  rw [show j - 1 + 1 = j by omega] at h3
  apply hne
  rw [eq_bot_iff]
  exact (Subgroup.lowerCentralSeries_antitone _ (by omega : j ≤ m - 2)).trans h3.le

theorem isMaximalClass_quotient_center {p : ℕ} [hp : Fact p.Prime] {P : Type u} [Group P]
    [Finite P] (hP : IsPGroup p P) (hmax : IsMaximalClass p P) (h3 : p ^ 3 ≤ Nat.card P) :
    IsMaximalClass p (P ⧸ Subgroup.center P) := by
  obtain ⟨m, hm2, hcard, hne⟩ := hmax
  have hm : 3 ≤ m := by
    rw [hcard] at h3
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp h3
  have hZ := card_center_of_maxClass hP hm hcard hne
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
  have hQ : Nat.card (P ⧸ Subgroup.center P) = p ^ (m - 1) := by
    have : p ^ m = p ^ (m - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hZ, hcard, this] at hmul
    exact (Nat.eq_of_mul_eq_mul_right hp.out.pos hmul).symm
  refine ⟨m - 1, by omega, hQ, fun hbot => hne ?_⟩
  have h1 := lcs_le_of_quotient_eq_bot _ (show (⊤ : Subgroup (P ⧸ Subgroup.center P)).lowerCentralSeries
    (m - 1 - 2) = ⊥ from hbot)
  have h2 := lcs_succ_eq_bot_of_le_center h1
  rwa [show m - 1 - 2 + 1 = m - 2 by omega] at h2

end CFSG.HardMathSupport.Lang.E6Descent
