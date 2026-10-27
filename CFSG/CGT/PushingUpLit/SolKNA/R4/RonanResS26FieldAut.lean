module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

theorem fieldAut_invol_eq_pow {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ q : ℕ, q * q = Nat.card K ∧ ∀ x : K, σ x = x ^ q := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite K p
  haveI hpF : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Fintype (ZMod p) := Fintype.ofFinite _
  have hcard : p ^ Module.finrank (ZMod p) K = Nat.card K :=
    FiniteField.pow_finrank_eq_natCard p K
  have hcomm : ∀ x : ZMod p, σ (algebraMap (ZMod p) K x) = algebraMap (ZMod p) K x := by
    intro x
    have h : σ.toRingHom.comp (algebraMap (ZMod p) K) = algebraMap (ZMod p) K :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x
  obtain ⟨τ, hτdef⟩ : ∃ τ : K ≃ₐ[ZMod p] K, ∀ x, τ x = σ x :=
    ⟨AlgEquiv.ofRingEquiv (f := σ) hcomm, fun x => rfl⟩
  have hτ2 : τ * τ = 1 := by
    ext x
    have h := congrArg (fun g : K ≃+* K => g x) hσ2
    rw [AlgEquiv.mul_apply, hτdef, hτdef]
    exact h
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hσ1
    ext x
    have h' := congrArg (fun g : K ≃ₐ[ZMod p] K => g x) h
    rw [← hτdef]
    exact h'
  obtain ⟨φ, hφdef⟩ : ∃ φ : K ≃ₐ[ZMod p] K,
      φ = FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K := ⟨_, rfl⟩
  have hord : orderOf φ = Module.finrank (ZMod p) K := by
    rw [hφdef]
    exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) K
  obtain ⟨a, ha⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) K).2 τ
  obtain ⟨j, hjτ⟩ : ∃ j : ℕ, φ ^ j = τ := ⟨a.1, by rw [hφdef]; exact ha⟩
  have h1 : φ ^ (j * 2) = 1 := by
    rw [pow_mul, hjτ, sq, hτ2]
  have h2 : ¬ orderOf φ ∣ j := by
    intro hd
    apply hτ1
    rw [← hjτ, orderOf_dvd_iff_pow_eq_one.mp hd]
  have h3 : orderOf φ ∣ j * 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
  rw [hord] at h2 h3
  obtain ⟨k, hk⟩ : 2 ∣ Module.finrank (ZMod p) K := by
    by_contra hodd
    have hc : Nat.Coprime (Module.finrank (ZMod p) K) 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    exact h2 (hc.dvd_of_dvd_mul_right h3)
  have h5 : k ∣ j := by
    have h3' : 2 * k ∣ 2 * j := by
      rw [← hk, mul_comm 2 j]
      exact h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3'
  obtain ⟨t, rfl⟩ := h5
  have ht : Odd t := by
    rcases Nat.even_or_odd t with ⟨s, hs⟩ | ht
    · exfalso
      apply h2
      refine ⟨s, ?_⟩
      rw [hk, hs]
      ring
    · exact ht
  obtain ⟨s, rfl⟩ := ht
  have hφf : φ ^ Module.finrank (ZMod p) K = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one φ
  have hτk : τ = φ ^ k := by
    rw [← hjτ]
    have hexp : k * (2 * s + 1) = k + Module.finrank (ZMod p) K * s := by
      rw [hk]
      ring
    rw [hexp, pow_add, pow_mul, hφf, one_pow, mul_one]
  have hiter : ∀ (n : ℕ) (x : K), (φ ^ n) x = x ^ (p ^ n) := by
    intro n x
    rw [hφdef, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]
  refine ⟨p ^ k, ?_, fun x => ?_⟩
  · rw [← hcard, hk, two_mul, pow_add]
  · have h : τ x = (φ ^ k) x := by rw [hτk]
    rw [← hτdef, h, hiter]

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
