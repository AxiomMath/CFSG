module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (centerQuotient_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem aor_mem_of_pow_mem_of_index_eq_two_pow {A : Type*} [Group A] {I : Subgroup A} [I.Normal]
    {m : ℕ} (hI : I.index = 2 ^ m) {a : A} {k : ℕ} (hk : Odd k) (ha : a ^ k ∈ I) : a ∈ I := by
  have hc : Nat.card (A ⧸ I) = 2 ^ m := hI
  have : Finite (A ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  set b : A ⧸ I := (a : A ⧸ I)
  have hb : b ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have h1 : orderOf b ∣ k := orderOf_dvd_of_pow_eq_one hb
  have h2 : orderOf b ∣ 2 ^ m := hc ▸ orderOf_dvd_natCard b
  have hcop : Nat.Coprime k (2 ^ m) := Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hk)
  have h3 : orderOf b = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff a).mp h3

theorem aor_conj_range_of_card_outer_dvd {X : Type} [Group X] (hX : Group.IsPerfect X) {m : ℕ}
    (h : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (X ⧸ center X)) ∣ 2 ^ m) :
    ∀ (α : MulAut X) (k : ℕ), Odd k → α ^ k ∈ (MulAut.conj : X →* MulAut X).range →
      α ∈ (MulAut.conj : X →* MulAut X).range := by
  intro α k hk hα
  haveI := hX
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  have hidx :
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (X ⧸ center X)).index = 2 ^ j := hj
  set Φ := centerQuotientHom X with hΦdef
  have hΦconj : ∀ x : X, Φ (MulAut.conj x) = MulAut.conj (QuotientGroup.mk' (center X) x) :=
    fun x => centerQuotient_conj x
  have hΦ : Function.Injective Φ := centerQuotientHom_injective X
  have hI : (CFSG.ComponentClassification.OuterAutomorphisms.inner (X ⧸ center X)).comap Φ =
      (MulAut.conj : X →* MulAut X).range := by
    ext β
    rw [mem_comap]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center X) y
      exact ⟨x, hΦ ((hΦconj x).trans hy)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hΦconj x).symm⟩
  rw [← hI] at hα ⊢
  rw [mem_comap, map_pow] at hα
  exact aor_mem_of_pow_mem_of_index_eq_two_pow hidx hk hα

end CFSG.OddStandard.SmallF3.Omega
