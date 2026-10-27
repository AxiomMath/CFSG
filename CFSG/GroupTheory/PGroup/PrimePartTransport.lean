module

public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem not_dvd_card_of_pRank_eq_zero {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (h : CFSG.Open.pRank p H = 0) : ¬ p ∣ Nat.card H := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p hdvd
  have hxordG : orderOf ((x : H) : G) = p := by
    rw [Subgroup.orderOf_coe, hxord]
  have hcard : Nat.card (Subgroup.zpowers ((x : H) : G)) = p := by
    rw [Nat.card_zpowers, hxordG]
  have hE : CFSG.Open.IsElemAbelian p (Subgroup.zpowers ((x : H) : G)) :=
    isElemAbelian_of_card_prime hcard
  have h1 : 1 ≤ CFSG.Open.pRank p H :=
    CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.mpr x.2) hE
      (by rw [hcard, pow_one])
  omega

theorem factorization_eq_of_surjective_ker_not_dvd {p : ℕ} {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (f : A →* B) (hf : Function.Surjective f)
    (hker : ¬ p ∣ Nat.card f.ker) :
    (Nat.card B).factorization p = (Nat.card A).factorization p := by
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  have hcard : Nat.card A = Nat.card B * Nat.card f.ker := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have hq : Nat.card (A ⧸ f.ker) = Nat.card B := by
      calc Nat.card (A ⧸ f.ker) = Nat.card ↥f.range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
        _ = Nat.card ↥(⊤ : Subgroup B) := by rw [hrange]
        _ = Nat.card B := Subgroup.card_top
    rw [h, hq]
  rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hker, add_zero]

theorem factorization_eq_of_forall_isPGroup_zpowers_mem {p : ℕ} (hp : p.Prime) {H K : Subgroup G}
    (hHK : H ≤ K) (hmem : ∀ x ∈ K, IsPGroup p (Subgroup.zpowers x) → x ∈ H) :
    (Nat.card K).factorization p = (Nat.card H).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf p K
  have hSK : S ≤ K := hS.le
  have hSH : S ≤ H := by
    intro x hx
    exact hmem x (hSK hx) (hS.isPGroup.to_le (Subgroup.zpowers_le.mpr hx))
  have hSdvdH : Nat.card S ∣ Nat.card H := Subgroup.card_dvd_of_le hSH
  have hScard : Nat.card S = p ^ (Nat.card K).factorization p := hS.card_eq
  have hle1 : (Nat.card K).factorization p ≤ (Nat.card H).factorization p := by
    rw [hScard] at hSdvdH
    exact (hp.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp hSdvdH
  have hle2 : (Nat.card H).factorization p ≤ (Nat.card K).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hHK) p
  omega

theorem mem_of_pow_two_pow_mem_of_orderOf_dvd_prime_pow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {A : Type*} [Group A] [Finite A] {I : Subgroup A} {ψ : A} {m : ℕ}
    (hψ : orderOf ψ ∣ r ^ m)
    {k : ℕ} (h : ψ ^ (2 ^ k) ∈ I) : ψ ∈ I := by
  by_cases hψ1 : ψ = 1
  · simpa [hψ1] using I.one_mem
  have hord1 : 1 < orderOf ψ := by
    have hpos : 0 < orderOf ψ := orderOf_pos ψ
    have hne : orderOf ψ ≠ 1 := fun h1 => hψ1 (orderOf_eq_one_iff.mp h1)
    omega
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hr).mp hψ
  have hcop : Nat.Coprime (2 ^ k) (orderOf ψ) := by
    rw [ha]
    have h2r : Nat.Coprime 2 r := Nat.prime_two.coprime_iff_not_dvd.mpr fun h2dvd =>
      hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2dvd).symm
    exact (h2r.pow_left k).pow_right a
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hord1
  have hψeq : ψ = (ψ ^ (2 ^ k)) ^ t := by
    rw [← pow_mul, ← pow_mod_orderOf, ht, pow_one]
  rw [hψeq]
  exact I.pow_mem h t

end CFSG.GroupTheory
