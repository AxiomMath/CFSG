module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.GaloisBlockStability

public section

namespace CFSG.LyonsUnitaryFour

open IntermediateField CFSG.TwoRankLowerBound.Helpers

variable {p e M N k : ℕ} {ζ : ℂ}

theorem pow_eq_self_of_pow_prime_pow {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    (hN : N = p ^ e * M) (hpM : ¬ p ∣ M) (hGN : Nat.card G ∣ N) (hk1 : k ≡ 1 [MOD p ^ e])
    {g : G} {j : ℕ} (hg : g ^ (p ^ j) = 1) : g ^ k = g := by
  have h1 : orderOf g ∣ p ^ j := orderOf_dvd_of_pow_eq_one hg
  have h2 : orderOf g ∣ N := (orderOf_dvd_natCard g).trans hGN
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp h1
  have h3 : orderOf g ∣ p ^ e := by
    rw [hi] at h2 ⊢
    rw [hN] at h2
    exact (Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)).dvd_of_dvd_mul_right
      h2
  have hge : g ^ (p ^ e) = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
  simpa using pow_eq_pow_of_modEq hge hk1

theorem galois_apply_sum_pow [NeZero N] (hζ : IsPrimitiveRoot ζ N) {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {ξ : ℂ} (hξ : ξ ^ N = 1) (s : Finset ℕ)
    (n : ℕ → ℤ) {z : ℂ} (hz : z ∈ ℚ⟮ζ⟯) (hzs : z = ∑ i ∈ s, (n i : ℂ) * ξ ^ i) :
    ((σ ⟨z, hz⟩ : ℚ⟮ζ⟯) : ℂ) = ∑ i ∈ s, (n i : ℂ) * ξ ^ (k * i) := by
  set ξE : ℚ⟮ζ⟯ := ⟨ξ, mem_adjoin_of_pow_eq_one hζ hξ⟩
  have hzE : (⟨z, hz⟩ : ℚ⟮ζ⟯) = ∑ i ∈ s, (n i : ℚ⟮ζ⟯) * ξE ^ i := by
    apply Subtype.ext
    change z = _
    rw [hzs]
    push_cast
    rfl
  have hσξ : σ ξE = ξE ^ k := galois_apply_of_pow_eq_one hζ hσ (Subtype.ext (by simpa using hξ))
  rw [hzE, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_intCast, hσξ, ← pow_mul]
  push_cast
  rfl

theorem frobenius_apply_sum_pow (hN : N = p ^ e * M) (hM : 0 < M) (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ N) (hkp : k ≡ p [MOD M]) {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {ξ : ℂ} (hξ : ξ ^ M = 1) (s : Finset ℕ)
    (n : ℕ → ℤ) {z : ℂ} (hz : z ∈ ℚ⟮ζ⟯) (hzs : z = ∑ i ∈ s, (n i : ℂ) * ξ ^ i) :
    ((σ ⟨z, hz⟩ : ℚ⟮ζ⟯) : ℂ) = ∑ i ∈ s, (n i : ℂ) * ξ ^ (p * i) := by
  have : NeZero N := ⟨by rw [hN]; exact (Nat.mul_pos (pow_pos hp.pos e) hM).ne'⟩
  have hξN : ξ ^ N = 1 := by rw [hN, mul_comm, pow_mul, hξ, one_pow]
  rw [galois_apply_sum_pow hζ hσ hξN s n hz hzs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_mul, pow_mul, pow_eq_pow_of_modEq hξ hkp]

variable {G : Type*} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)

theorem frobenius_galois_block_stability (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (hp : p.Prime) (hN : N = p ^ e * M) (hpM : ¬ p ∣ M) (hM : 0 < M)
    (hGN : Nat.card G ∣ N) (hζ : IsPrimitiveRoot ζ N) (hk : k.Coprime N)
    (hk1 : k ≡ 1 [MOD p ^ e]) {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) :
    ∃ π : Equiv.Perm basis.index,
      (∀ a g, (basis.representation (π a)).character g =
        (basis.representation a).character (g ^ k)) ∧
      (∀ a g, ∃ h : (basis.representation a).character g ∈ ℚ⟮ζ⟯,
        ((σ ⟨(basis.representation a).character g, h⟩ : ℚ⟮ζ⟯) : ℂ) =
          (basis.representation (π a)).character g) ∧
      (∀ a, Module.finrank ℂ (basis.representation (π a)).vector =
        Module.finrank ℂ (basis.representation a).vector) ∧
      (∀ a b, sameCoefficientBlock basis (localizedComplexIntegerRing ideal) (π a) (π b) ↔
        sameCoefficientBlock basis (localizedComplexIntegerRing ideal) a b) ∧
      (∀ a, (coefficientBlock basis (localizedComplexIntegerRing ideal) a).map π.toEmbedding =
        coefficientBlock basis (localizedComplexIntegerRing ideal) (π a)) ∧
      (∀ a, (basis.representation a).character = 1 → π a = a) ∧
      (∀ a b, (basis.representation a).character = 1 →
        (π b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) a ↔
          b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) a)) ∧
      (∀ a (g : G) (j : ℕ), g ^ (p ^ j) = 1 →
        (basis.representation (π a)).character g = (basis.representation a).character g) := by
  have : NeZero N := ⟨by rw [hN]; exact (Nat.mul_pos (pow_pos hp.pos e) hM).ne'⟩
  obtain ⟨π, hπ, hσπ, hdeg, hblock, himage, hprin, hprinBlock⟩ :=
    galois_block_stability basis ideal hGN hζ hk hσ
  refine ⟨π, hπ, hσπ, hdeg, hblock, himage, hprin, hprinBlock, fun a g j hg => ?_⟩
  rw [hπ, pow_eq_self_of_pow_prime_pow hp hN hpM hGN hk1 hg]

end CFSG.LyonsUnitaryFour
