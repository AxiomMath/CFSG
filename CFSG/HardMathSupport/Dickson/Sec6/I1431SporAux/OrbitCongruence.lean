module

public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open MulAction

section OrbitCongruence

variable {P Ω : Type*} [Group P] [MulAction P Ω]

theorem eq_one_or_eq_of_dvd_pow_three {p s : ℕ} (hp : p.Prime) (hs : s ∣ p ^ 3) (hle : s ≤ p) :
    s = 1 ∨ s = p := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hs
  interval_cases i
  · left; simp
  · right; simp
  · exfalso
    have h := Nat.pow_lt_pow_right hp.one_lt (show 1 < 2 by norm_num)
    rw [pow_one] at h
    omega
  · exfalso
    have h := Nat.pow_lt_pow_right hp.one_lt (show 1 < 3 by norm_num)
    rw [pow_one] at h
    omega

theorem exists_mul_eq_sum_card_fixedBy [Fintype P] [Finite Ω] {p : ℕ} (hp : p.Prime)
    (hP : Fintype.card P = p ^ 3) (hstab : ∀ ω : Ω, Nat.card (stabilizer P ω) ≤ p) :
    ∃ K : ℕ, p * Nat.card Ω = ∑ g : P, Nat.card (fixedBy Ω g) + p ^ 3 * K := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  haveI : ∀ g : P, Fintype (fixedBy Ω g) := fun g => Fintype.ofFinite _
  haveI : ∀ ω : Ω, Fintype (stabilizer P ω) := fun ω => Fintype.ofFinite _
  haveI : Fintype (orbitRel.Quotient P Ω) := Fintype.ofFinite _
  have hclass := card_eq_sum_card_group_div_card_stabilizer P Ω
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group P Ω
  have hterm : ∀ q : orbitRel.Quotient P Ω, ∃ j : ℕ,
      p * (Fintype.card P / Fintype.card (stabilizer P q.out)) = p ^ 3 + p ^ 3 * j := by
    intro q
    have hd : Fintype.card (stabilizer P q.out) ∣ p ^ 3 := by
      rw [← hP, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card _
    have hl : Fintype.card (stabilizer P q.out) ≤ p := by
      rw [← Nat.card_eq_fintype_card]
      exact hstab _
    rcases eq_one_or_eq_of_dvd_pow_three hp hd hl with h | h
    · refine ⟨p - 1, ?_⟩
      rw [h, hP, Nat.div_one]
      have := hp.one_le
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    · refine ⟨0, ?_⟩
      rw [h, hP]
      have hpos : 0 < p := hp.pos
      have : p ^ 3 / p = p ^ 2 := by
        rw [pow_succ, Nat.mul_div_cancel _ hpos]
      rw [this]
      ring
  choose j hj using hterm
  refine ⟨∑ q, j q, ?_⟩
  have hsum : ∑ g : P, Nat.card (fixedBy Ω g) = ∑ g : P, Fintype.card (fixedBy Ω g) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Nat.card_eq_fintype_card]
  have key : ∑ q : orbitRel.Quotient P Ω, p * (Fintype.card P / Fintype.card (stabilizer P q.out)) =
      Fintype.card (orbitRel.Quotient P Ω) * Fintype.card P + p ^ 3 * ∑ q, j q := by
    calc ∑ q : orbitRel.Quotient P Ω, p * (Fintype.card P / Fintype.card (stabilizer P q.out)) =
        ∑ q : orbitRel.Quotient P Ω, (p ^ 3 + p ^ 3 * j q) :=
          Finset.sum_congr rfl fun q _ => hj q
      _ = Fintype.card (orbitRel.Quotient P Ω) * Fintype.card P + p ^ 3 * ∑ q, j q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP]
        simp [mul_comm]
  rw [Nat.card_eq_fintype_card, hclass, Finset.mul_sum, hsum, hburn]
  exact key

end OrbitCongruence

section Centralizer

variable {G : Type*} [Group G]

theorem card_inf_centralizer_le [Finite G] {p : ℕ} (hp : p.Prime) {S : Subgroup G}
    (hS : IsPGroup p S) {u : G} (hC : ¬ p ^ 2 ∣ Nat.card (Subgroup.centralizer ({u} : Set G))) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({u} : Set G)) ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hR : IsPGroup p ↥(S ⊓ Subgroup.centralizer ({u} : Set G)) :=
    hS.to_le inf_le_left
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn]
  by_contra hlt
  push Not at hlt
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n ≤ 1 := by omega
    interval_cases n
    · simp at hlt
      exact absurd hlt (by have := hp.two_le; omega)
    · simp at hlt
  apply hC
  have hdvd : Nat.card ↥(S ⊓ Subgroup.centralizer ({u} : Set G)) ∣
      Nat.card (Subgroup.centralizer ({u} : Set G)) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hn] at hdvd
  exact (pow_dvd_pow p hn2).trans hdvd

end Centralizer

end CFSG.HardMathSupport.Dickson.Sec6.I1431
