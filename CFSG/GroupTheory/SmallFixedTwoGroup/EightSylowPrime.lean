module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.FixedCount
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem prime_order_acts_on_order_eight {T : Subgroup G} (hT : Nat.card T = 8) {x : G}
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hx : x ^ r = 1)
    (hxN : x ∈ normalizer (T : Set G)) (hne : ¬ T ≤ centralizer ({x} : Set G)) :
    (r = 3 ∧ Nat.card (T ⊓ centralizer ({x} : Set G) : Subgroup G) = 2) ∨
      (r = 7 ∧ Nat.card (T ⊓ centralizer ({x} : Set G) : Subgroup G) = 1) := by
  have hrp : r.Prime := Fact.out
  have horder_dvd : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hx
  have horder : orderOf x = r := by
    rcases hrp.eq_one_or_self_of_dvd (orderOf x) horder_dvd with h1 | hr
    · exfalso
      apply hne
      intro t _
      rw [Subgroup.mem_centralizer_singleton_iff, orderOf_eq_one_iff.1 h1]
      simp
    · exact hr
  have hP : IsPGroup r (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horder, pow_one])
  have hPA : ∀ y ∈ zpowers x, ∀ a ∈ T, y * a * y⁻¹ ∈ T := by
    intro y hy a ha
    have hyN : y ∈ normalizer (T : Set G) := (Subgroup.zpowers_le.2 hxN) hy
    exact (Subgroup.mem_normalizer_iff.1 hyN a).1 ha
  have hcent : centralizer ((zpowers x : Subgroup G) : Set G) =
      centralizer ({x} : Set G) := by
    ext g
    rw [CFSG.LocalAnalysis.EvenBN.Tits.mem_centralizer_zpowers_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h
    · intro h
      exact h x rfl
  have hmod := CFSG.LocalAnalysis.EvenBN.Tits.card_modEq_card_inf_centralizer
    (Γ := G) (p := r) (P := zpowers x) (A := T) hP hPA
  rw [hcent, hT] at hmod
  set F : Subgroup G := T ⊓ centralizer ({x} : Set G) with hF
  have hFdvd : Nat.card F ∣ 8 := by
    rw [← hT]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have hFle : Nat.card F ≤ 8 := Nat.le_of_dvd (by norm_num) hFdvd
  have hFne8 : Nat.card F ≠ 8 := by
    intro h8
    have heq : F = T := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hne ((le_of_eq heq.symm).trans inf_le_right)
  have hFmem : Nat.card F = 1 ∨ Nat.card F = 2 ∨ Nat.card F = 4 := by
    have hdvd' : Nat.card F ∣ 2 ^ 3 := by
      rwa [show (2 : ℕ) ^ 3 = 8 by norm_num]
    obtain ⟨k, _hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd'
    interval_cases k
    · left; simpa using hFk
    · right; left; simpa using hFk
    · right; right; simpa using hFk
    · exact absurd (by simpa using hFk) hFne8
  have hdvd : r ∣ 8 - Nat.card F := (Nat.modEq_iff_dvd' hFle).1 hmod.symm
  rcases hFmem with h1 | h2 | h4
  · right
    refine ⟨?_, h1⟩
    have h7 : r ∣ 7 := by
      rw [h1] at hdvd
      norm_num at hdvd
      exact hdvd
    exact (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_seven).1 h7
  · left
    refine ⟨?_, h2⟩
    have h6 : r ∣ 6 := by
      rw [h2] at hdvd
      norm_num at hdvd
      exact hdvd
    rcases (hrp.dvd_mul (m := 2) (n := 3)).1
      (by rw [show (2 : ℕ) * 3 = 6 by norm_num]; exact h6) with h2d | h3d
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 h2d) hr2
    · exact (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).1 h3d
  · exfalso
    have h4' : r ∣ 4 := by
      rw [h4] at hdvd
      norm_num at hdvd
      exact hdvd
    have h2d : r ∣ 2 := hrp.dvd_of_dvd_pow
      (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4')
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 h2d)

theorem exists_mem_normalizer_orderOf_eq_of_prime_dvd_relIndex {T : Subgroup G} {r : ℕ}
    [Fact r.Prime] (h : r ∣ T.relIndex (normalizer (T : Set G))) :
    ∃ x ∈ normalizer (T : Set G), orderOf x = r := by
  let N : Subgroup G := normalizer (T : Set G)
  have hTN : (T.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let Q := N ⧸ T.subgroupOf N
  have hcard : Nat.card Q = T.relIndex N := rfl
  have hdvd : r ∣ Nat.card Q := by
    rw [hcard]
    exact h
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) r hdvd
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (T.subgroupOf N) q
  have hdvdn : r ∣ orderOf n := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (T.subgroupOf N)) n
    rw [hn, hq] at h1
    exact h1
  refine ⟨((n ^ (orderOf n / r) : ↥N) : G), (n ^ (orderOf n / r)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos n)) hdvdn

end CFSG.GroupTheory.SmallFixedTwoGroup
