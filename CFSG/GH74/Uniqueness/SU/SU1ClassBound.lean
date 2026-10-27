module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {p : ℕ}

theorem isCyclic_of_card_le_prime (hp : p.Prime) {Q : Type*} [Group Q] [Finite Q] {k : ℕ}
    (hQ : Nat.card Q = p ^ k) (hk : k ≤ 1) : IsCyclic Q := by
  have := Fact.mk hp
  rcases Nat.lt_or_ge k 1 with h0 | h1
  · have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hQ
    have : Subsingleton Q := Finite.card_le_one_iff_subsingleton.mp hQ.le
    infer_instance
  · have hk1 : k = 1 := by omega
    rw [hk1, pow_one] at hQ
    have : Fact (Nat.card Q).Prime := ⟨hQ ▸ hp⟩
    exact isCyclic_of_prime_card hQ

theorem nilpotencyClass_le_of_card (hp : p.Prime) :
    ∀ j : ℕ, ∀ (Q : Type) [Group Q] [Finite Q], Nat.card Q = p ^ j → 2 ≤ j →
      Group.nilpotencyClass Q ≤ j - 1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro Q _ _ hQ hj
  have := Fact.mk hp
  have hQp : IsPGroup p Q := IsPGroup.of_card hQ
  have hnil : Group.IsNilpotent Q := hQp.isNilpotent
  by_cases hcomm : IsMulCommutative Q
  · have := (Group.IsNilpotent.nilpotencyClass_le_one_iff).mpr hcomm
    omega
  · have hnt : Nontrivial Q := by
      rw [← Finite.one_lt_card_iff_nontrivial, hQ]
      exact Nat.one_lt_pow (by omega) hp.one_lt
    have hZnt : Nontrivial (center Q) := hQp.center_nontrivial
    have hdvd : Nat.card (center Q) ∣ p ^ j := hQ ▸ Subgroup.card_subgroup_dvd_card (center Q)
    obtain ⟨s, hsj, hs⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hZ1 : 1 < Nat.card (center Q) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
    have hs1 : 1 ≤ s := by
      by_contra hcon
      have : s = 0 := by omega
      rw [hs, this, pow_zero] at hZ1
      exact lt_irrefl _ hZ1
    have hQZ : Nat.card (Q ⧸ center Q) = p ^ (j - s) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
      rw [hs, hQ] at h1
      have h2 : p ^ j = p ^ (j - s) * p ^ s := by
        rw [← pow_add, Nat.sub_add_cancel hsj]
      rw [h2] at h1
      exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos s) h1).symm
    have hj2 : 2 ≤ j - s := by
      by_contra hcon
      have hcyc : IsCyclic (Q ⧸ center Q) := isCyclic_of_card_le_prime hp hQZ (by omega)
      exact hcomm (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (center Q)) (by simp))
    have hih := ih (j - s) (by omega) (Q ⧸ center Q) hQZ hj2
    rw [Group.nilpotencyClass_quotient_center] at hih
    omega

theorem card_center_of_maxClass (hp : p.Prime) {n : ℕ} (hn : 4 ≤ n) {P : Type} [Group P]
    [Finite P] (hP : Nat.card P = p ^ n) (hcl : n - 1 ≤ Group.nilpotencyClass P) :
    Nat.card (center P) = p := by
  have := Fact.mk hp
  have hPp : IsPGroup p P := IsPGroup.of_card hP
  have hnil : Group.IsNilpotent P := hPp.isNilpotent
  have hnt : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial, hP]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have hZnt : Nontrivial (center P) := hPp.center_nontrivial
  have hdvd : Nat.card (center P) ∣ p ^ n := hP ▸ Subgroup.card_subgroup_dvd_card (center P)
  obtain ⟨s, hsn, hs⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hZ1 : 1 < Nat.card (center P) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
  have hs1 : 1 ≤ s := by
    by_contra hcon
    have : s = 0 := by omega
    rw [hs, this, pow_zero] at hZ1
    exact lt_irrefl _ hZ1
  have hQZ : Nat.card (P ⧸ center P) = p ^ (n - s) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center P)
    rw [hs, hP] at h1
    have h2 : p ^ n = p ^ (n - s) * p ^ s := by
      rw [← pow_add, Nat.sub_add_cancel hsn]
    rw [h2] at h1
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos s) h1).symm
  have hcq := Group.nilpotencyClass_quotient_center (G := P)
  have hns2 : 2 ≤ n - s := by
    by_contra hcon
    have hcyc : IsCyclic (P ⧸ center P) := isCyclic_of_card_le_prime hp hQZ (by omega)
    have hcomm : IsMulCommutative (P ⧸ center P) := inferInstance
    have hnilQ : Group.IsNilpotent (P ⧸ center P) := IsPGroup.isNilpotent (hPp.to_quotient _)
    have := (Group.IsNilpotent.nilpotencyClass_le_one_iff (G := P ⧸ center P)).mpr hcomm
    omega
  have hb := nilpotencyClass_le_of_card hp (n - s) (P ⧸ center P) hQZ hns2
  have hs2 : s = 1 := by omega
  rw [hs, hs2, pow_one]

end CFSG.GH74.Uniqueness.SU.SU1
