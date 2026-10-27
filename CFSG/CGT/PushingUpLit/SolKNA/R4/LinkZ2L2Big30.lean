module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big6

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section FrobTwo

variable {F : Type} [Field F] [Finite F] {p f : ℕ}

theorem exists_frobenius_two_power [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (hf : Even f) (hf0 : f ≠ 0) {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1)
    (hq : ∀ x : F, σ₀ x = x ^ p ^ (f / 2)) :
    ∃ (e s : ℕ) (ψ : F ≃+* F), 1 ≤ e ∧ padicValNat 2 f = e ∧ orderOf ψ = 2 ^ e ∧
      (∀ x : F, ψ x = x ^ s) ∧ Odd s ∧ s ^ 2 ^ e = p ^ f ∧ ψ ^ 2 ^ (e - 1) = σ₀ := by
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hchar : CharP F p := charP_of_card_eq_prime_pow hcardF
  obtain ⟨e, f₀, hf₀odd, hfe⟩ := Nat.exists_eq_two_pow_mul_odd hf0
  have he : 1 ≤ e := by
    by_contra h
    have he0 : e = 0 := by omega
    have hfodd : Odd f := by rw [hfe, he0]; simpa using hf₀odd
    exact (Nat.not_even_iff_odd.mpr hfodd) hf
  have hf₀ne : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hf₀odd
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2f₀ : ¬ 2 ∣ f₀ := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hf₀odd) (even_iff_two_dvd.mpr h)
  have hpval : padicValNat 2 f = e := by
    rw [hfe, padicValNat.mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hf₀ne,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd h2f₀]
    omega
  have hsodd : Odd (p ^ f₀) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  let ψ : F ≃+* F := RingEquiv.ofBijective (iterateFrobenius F p f₀)
    ⟨RingHom.injective _, Finite.surjective_of_injective (RingHom.injective _)⟩
  have hψ : ∀ x : F, ψ x = x ^ (p ^ f₀) := fun x => iterateFrobenius_def p f₀ x
  have hpow : ∀ (j : ℕ) (x : F), (ψ ^ j) x = x ^ (p ^ f₀) ^ j := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hψ, ih, ← pow_mul, pow_succ, mul_comm]
  have hspow : (p ^ f₀) ^ 2 ^ e = p ^ f := by
    rw [← pow_mul, hfe]
    congr 1
    exact Nat.mul_comm _ _
  have hψpow : ψ ^ 2 ^ e = 1 := by
    ext x
    rw [hpow (2 ^ e) x, hspow, RingAut.one_apply, ← hF, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hpow2 : 2 ^ e = 2 ^ (e - 1) * 2 := by
    nth_rewrite 1 [← Nat.sub_add_cancel he]
    rw [pow_succ]
  have hfd : f = 2 * (2 ^ (e - 1) * f₀) := by
    rw [hfe, hpow2]
    ring
  have hdiv : f / 2 = 2 ^ (e - 1) * f₀ := by omega
  have hexp : (p ^ f₀) ^ 2 ^ (e - 1) = p ^ (f / 2) := by
    rw [← pow_mul, hdiv]
    congr 1
    exact Nat.mul_comm _ _
  have hψhalf : ψ ^ 2 ^ (e - 1) = σ₀ := by
    ext x
    rw [hpow (2 ^ (e - 1)) x, hexp, hq x]
  have horder : orderOf ψ = 2 ^ e := by
    have hnot : ¬ ψ ^ 2 ^ (e - 1) = 1 := by
      rw [hψhalf]
      exact hσ₀1
    have hfin : ψ ^ 2 ^ (e - 1 + 1) = 1 := by
      rw [Nat.sub_add_cancel he]
      exact hψpow
    have h := orderOf_eq_prime_pow (p := 2) (n := e - 1) (x := ψ) hnot hfin
    rwa [Nat.sub_add_cancel he] at h
  exact ⟨e, p ^ f₀, ψ, he, hpval, horder, hψ, hsodd, hspow, hψhalf⟩

end FrobTwo

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
