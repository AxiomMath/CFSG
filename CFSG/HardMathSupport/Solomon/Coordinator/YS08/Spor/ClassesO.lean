module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Classes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def L3ExclD (N q d : ℕ) : Prop :=
  ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε → L3Ord r ε ∣ N * e →
    q ∣ L3Ord r ε ∧ ¬ d ∣ L3Ord r ε

@[expose] def L3ExclDCheck (N q d B : ℕ) : Bool :=
  (List.range B).all fun i => [true, false].all fun ε => [1, 3].all fun e =>
    decide (l3CondB (i + 4) ε = true → L3Ord (i + 4) ε ∣ N * e →
      q ∣ L3Ord (i + 4) ε ∧ ¬ d ∣ L3Ord (i + 4) ε)

theorem l3ExclD_of_check {N q d B : ℕ} (hN : 0 < N) (hB : 12 * N < (B + 4) ^ 8)
    (h : L3ExclDCheck N q d B = true) : L3ExclD N q d := by
  intro r ε e he hc hdvd
  have hr4 : 4 ≤ r := by
    cases ε
    · exact le_trans (by norm_num) (hc.2 rfl).1
    · exact (hc.1 rfl).1
  have hle : L3Ord r ε ≤ N * e := Nat.le_of_dvd (by rcases he with rfl | rfl <;> omega) hdvd
  have hrB : r < B + 4 := by
    by_contra hge
    push Not at hge
    have h1 : (B + 4) ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hge 8
    have h2 := L3Ord_pow_le hc
    have h3 : 4 * (N * e) ≤ 12 * N := by rcases he with rfl | rfl <;> omega
    omega
  have hall := List.all_eq_true.1 h (r - 4) (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 hall ε (by cases ε <;> simp)
  have h3 := List.all_eq_true.1 h2 e (by rcases he with rfl | rfl <;> simp)
  have hr : r - 4 + 4 = r := by omega
  rw [hr] at h3
  exact of_decide_eq_true h3 (l3CondB_of_cond hc) hdvd

theorem noL3Comp_of_prime_pair_O {G : Type} [Group G] [Finite G] {P C : Subgroup G} {q d : ℕ}
    (hO : GLAPPrimeCoreOf 3 C = ⊥) (hCP : C ≤ P) (hq : q.Prime) (hq3 : q ≠ 3)
    (hN : L3ExclD (Nat.card ↥P) q d) (hqq : ¬ q ^ 2 ∣ Nat.card ↥C)
    (hpair : ∃ a ∈ C, ∃ b ∈ C, orderOf a = q ∧ orderOf b = q ∧
      d ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set G))) :
    NoL3Comp C := by
  intro J hJ p hL
  obtain ⟨r, ε, e, he, hc, hcard⟩ := isL3Kind_card_forms hL
  have hbar := card_barOf_of_glaPComponent hO hJ
  have hdvdC : Nat.card (barOf 3 J) ∣ Nat.card ↥C := by
    rw [hbar]
    exact Subgroup.card_dvd_of_le hJ.1
  have hdvdM : Nat.card (barOf 3 J) ∣ Nat.card ↥P := hdvdC.trans (Subgroup.card_dvd_of_le hCP)
  have hL3 : L3Ord r ε ∣ Nat.card ↥P * e := by
    rw [← hcard]
    exact Nat.mul_dvd_mul_right hdvdM e
  obtain ⟨hqL, hd⟩ := hN r ε e he hc hL3
  rw [← hcard] at hqL hd
  have hqJbar : q ∣ Nat.card (barOf 3 J) := by
    rcases (Nat.Prime.dvd_mul hq).1 hqL with h | h
    · exact h
    · exfalso
      rcases he with rfl | rfl
      · exact hq.one_lt.ne' (Nat.dvd_one.1 h)
      · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)
  have hqJ : q ∣ Nat.card ↥J := by
    rw [← hbar]
    exact hqJbar
  have hmulC : Nat.card ↥J * J.relIndex C = Nat.card ↥C := by
    have h1 := Subgroup.card_mul_index (J.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ.1).toEquiv] at h1
    exact h1
  have hrel : ¬ q ∣ J.relIndex C := by
    intro hr
    apply hqq
    rw [← hmulC, pow_two]
    exact Nat.mul_dvd_mul hqJ hr
  obtain ⟨a, haC, b, hbC, hao, hbo, h3⟩ := hpair
  have hcopq : Nat.Coprime q (J.relIndex C) := (Nat.Prime.coprime_iff_not_dvd hq).2 hrel
  have haJ : a ∈ J := mem_of_isSubnormal_of_coprime hJ.2.1 haC (by rw [hao]; exact hcopq)
  have hbJ : b ∈ J := mem_of_isSubnormal_of_coprime hJ.2.1 hbC (by rw [hbo]; exact hcopq)
  have hHJ : Subgroup.closure ({a, b} : Set G) ≤ J := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact haJ
    · exact hbJ
  have hdJ : d ∣ Nat.card ↥J := h3.trans (Subgroup.card_dvd_of_le hHJ)
  have hdJ' : d ∣ Nat.card (barOf 3 J) := by
    rw [hbar]
    exact hdJ
  exact hd (hdJ'.mul_right e)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
