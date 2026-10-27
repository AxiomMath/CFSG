module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

variable {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}

theorem dvd_exponent_of_fieldElt {H : Subgroup (GL ι K)} {φ : ↥H →* Ω}
    {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K} {θ : ↥(innerPart S B) →* ↥H} {b : Ω} {A : GL ι K}
    {σ : K ≃+* K} (hF : FieldElt p S B φ β θ b A σ) {Q : TauCeti.PrimePower}
    (hK : Nat.card K = Q.card) : p ∣ Q.exponent := by
  have hcard := hF.2.2.2.2.1.2.1
  rw [hK, TauCeti.PrimePower.card_def] at hcard
  set n := Nat.card ↥(CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) with hn
  have hℓ := Q.prime_p
  have he := Q.exponent_pos
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    have : 1 < Q.p ^ Q.exponent := Nat.one_lt_pow he.ne' hℓ.one_lt
    omega
  have hdvd : n ∣ Q.p ^ Q.exponent := hcard ▸ dvd_pow_self n hp0
  obtain ⟨r₀, -, hr₀⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
  rw [hr₀, ← pow_mul] at hcard
  exact ⟨r₀, by rw [Nat.pow_right_injective hℓ.two_le hcard, mul_comm]⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
