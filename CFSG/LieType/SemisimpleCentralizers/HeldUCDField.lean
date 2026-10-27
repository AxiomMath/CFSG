module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

theorem sigma_eq_frobenius_pow {L K : Type} [Field L] [Finite L] [Field K] [Finite K]
    [Algebra L K] {Q : ℕ} (hQ : Nat.card L = Q ^ 2) (τ : L ≃+* L) (hτQ : ∀ x : L, τ x = x ^ Q)
    (σ : K ≃+* K) (hσ : ∀ l : L, σ (algebraMap L K l) = algebraMap L K (τ l))
    (hσσ : ∀ x : K, σ (σ x) = x) :
    ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ Q = p ^ e ∧ Odd (Module.finrank L K) ∧
      Nat.card K = Q ^ (2 * Module.finrank L K) ∧
      ∀ x : K, σ x = x ^ (Q ^ Module.finrank L K) := by
  classical
  set p := ringChar L with hpdef
  have hp : p.Prime := CharP.char_is_prime L p
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP L p := ringChar.charP L
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap L K).injective p
  haveI : Fintype L := Fintype.ofFinite L
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Module.Finite L K := Module.Finite.of_finite
  letI : Algebra (ZMod p) K := (ZMod.castHom dvd_rfl K).toAlgebra
  letI : Algebra (ZMod p) L := (ZMod.castHom dvd_rfl L).toAlgebra
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card L = p ^ m := by
    obtain ⟨n, -, hn⟩ := FiniteField.card L p
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hL1 : 1 < Nat.card L := Finite.one_lt_card
  have hQdvd : Q ∣ p ^ m := by
    have : Q ∣ Nat.card L := hQ ▸ dvd_pow_self Q two_ne_zero
    rwa [hm] at this
  obtain ⟨e, -, hQe⟩ := (Nat.dvd_prime_pow hp).1 hQdvd
  have hcard2 : Nat.card L = p ^ (2 * e) := by rw [hQ, hQe, ← pow_mul, mul_comm]
  have hm2 : m = 2 * e := Nat.pow_right_injective hp.two_le (hm.symm.trans hcard2)
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      rw [hQe, pow_zero] at hQ
      rw [hQ] at hL1
      omega
    · exact h
  set k := Module.finrank L K with hkdef
  have hK : Nat.card K = p ^ (2 * e * k) := by
    rw [Module.natCard_eq_pow_finrank (K := L) (V := K), hcard2, ← pow_mul]
  have hLp : Module.finrank (ZMod p) L = 2 * e := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := L)
    rw [hcard2, Nat.card_zmod] at this
    exact (Nat.pow_right_injective hp.two_le this).symm
  have hKp : Module.finrank (ZMod p) K = 2 * e * k := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := K)
    rw [hK, Nat.card_zmod] at this
    exact (Nat.pow_right_injective hp.two_le this).symm
  set φK := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K with hφK
  set φL := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L with hφL
  have hφK_iter : ∀ (j : ℕ) (x : K), (φK ^ j) x = x ^ (p ^ j) := by
    intro j x
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  have hφL_iter : ∀ (j : ℕ) (x : L), (φL ^ j) x = x ^ (p ^ j) := by
    intro j x
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  have hordK : orderOf φK = 2 * e * k := by
    rw [hφK, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hKp]
  have hordL : orderOf φL = 2 * e := by
    rw [hφL, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hLp]
  let g : K ≃ₐ[ZMod p] K := AlgEquiv.ofRingEquiv (f := σ) (fun z => by
    have h := RingHom.ext_zmod ((σ : K →+* K).comp (algebraMap (ZMod p) K))
      (algebraMap (ZMod p) K)
    exact congrArg (fun F => F z) h)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p K g
  rw [Nat.card_zmod] at hi
  have hσi : ∀ x : K, σ x = x ^ (p ^ i) := fun x => hi x
  have hgφ : g = φK ^ i := by
    ext x
    rw [hφK_iter]
    exact hi x
  have hg2 : φK ^ (2 * i) = 1 := by
    ext x
    rw [pow_mul', ← hgφ, pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact hσσ x
  have hdvd : 2 * e * k ∣ 2 * i := by
    rw [← hordK]
    exact orderOf_dvd_of_pow_eq_one hg2
  have hekdvd : e * k ∣ i := by
    have : 2 * (e * k) ∣ 2 * i := by
      rw [show 2 * e * k = 2 * (e * k) by ring] at hdvd
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  obtain ⟨u, hu⟩ := hekdvd
  have hLi : ∀ l : L, l ^ (p ^ i) = l ^ (p ^ e) := by
    intro l
    apply (algebraMap L K).injective
    rw [map_pow, map_pow, ← hσi, hσ, hτQ, map_pow, hQe]
  have hψ : φL ^ i = φL ^ e := by
    ext l
    rw [hφL_iter, hφL_iter]
    exact hLi l
  have hmod : i ≡ e [MOD 2 * e] := by
    rw [← hordL]
    exact pow_eq_pow_iff_modEq.mp hψ
  have hodd : Odd (k * u) := by
    have h1 : i % (2 * e) = e := by
      have := hmod
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [hu, show e * k * u = e * (k * u) by ring, show 2 * e = e * 2 by ring,
      Nat.mul_mod_mul_left] at h1
    have h2 : (k * u) % 2 = 1 := by
      have : e * ((k * u) % 2) = e * 1 := by rw [mul_one]; exact h1
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    exact Nat.odd_iff.mpr h2
  obtain ⟨hkodd, huodd⟩ := Nat.odd_mul.mp hodd
  refine ⟨p, e, hp, he, hQe, hkodd, ?_, ?_⟩
  · rw [hK, hQe, ← pow_mul]
    congr 1
    ring
  · intro x
    obtain ⟨v, hv⟩ := huodd
    have h2ek : φK ^ (2 * e * k) = 1 := by
      rw [← hordK]
      exact pow_orderOf_eq_one φK
    have hpow : φK ^ i = φK ^ (e * k) := by
      rw [hu, hv, show e * k * (2 * v + 1) = e * k + (2 * e * k) * v by ring, pow_add,
        pow_mul φK (2 * e * k) v, h2ek, one_pow, mul_one]
    rw [hσi, ← hφK_iter i x, hpow, hφK_iter (e * k) x, hQe, ← pow_mul]

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
