module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.LieType.Ree

theorem zpow_bijective_of_isCoprime {G : Type*} [Group G] [Finite G] {k : ℤ}
    (h : IsCoprime k (Nat.card G)) : Function.Bijective fun s : G => s ^ k := by
  obtain ⟨u, v, huv⟩ := h
  have key : ∀ s : G, s ^ (u * k) = s := fun s => by
    rw [show u * k = 1 - v * (Nat.card G : ℤ) by linear_combination huv, zpow_sub, zpow_one,
      mul_comm v, zpow_mul, zpow_natCast, pow_card_eq_one', one_zpow, inv_one, mul_one]
  refine Function.bijective_iff_has_inverse.2 ⟨fun s => s ^ u, fun s => ?_, fun s => ?_⟩
  · simp only
    rw [← zpow_mul, mul_comm, key]
  · simp only
    rw [← zpow_mul, key]

theorem iterate_pow_eq_pow (m n : ℕ) {M : Type*} [Monoid M] (x : M) :
    (fun y : M => y ^ m)^[n] x = x ^ m ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ]

theorem suzuki_frobenius_exponents (a : ℕ) (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CharP K 2 ∧
    (∃ φ : K ≃+* K, ∀ x, φ x = x ^ 2 ^ (a + 1)) ∧
    (∀ x : K, (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2) ∧
    (∀ x : K, (fun y : K => y ^ 2 ^ (a + 1))^[2 * a + 1] x = x) ∧
    Int.gcd (2 ^ (a + 1) - 1) (2 ^ (2 * a + 1) - 1) = 1 ∧
    Int.gcd (2 ^ (a + 1) + 1) (2 ^ (2 * a + 1) - 1) = 1 ∧
    Int.gcd (2 - 2 ^ (a + 1)) (2 ^ (2 * a + 1) - 1) = 1 ∧
    Int.gcd (1 + 2 ^ a) (2 ^ (2 * a + 1) - 1) = 1 ∧
    (2 - 2 ^ (a + 1) : ℤ) * (1 + 2 ^ a) ≡ 1 [ZMOD 2 ^ (2 * a + 1) - 1] ∧
    Function.Bijective (fun s : Kˣ => s ^ (2 ^ (a + 1) - 1 : ℤ)) ∧
    Function.Bijective (fun s : Kˣ => s ^ (2 ^ (a + 1) + 1 : ℤ)) ∧
    Function.Bijective (fun s : Kˣ => s ^ (2 - 2 ^ (a + 1) : ℤ)) ∧
    Function.Bijective (fun s : Kˣ => s ^ (1 + 2 ^ a : ℤ)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow hcard
  have hq : ∀ x : K, x ^ 2 ^ (2 * a + 1) = x := fun x => by
    rw [← hcard, FiniteField.pow_card]
  have h1 : IsCoprime (2 ^ (a + 1) - 1 : ℤ) (2 ^ (2 * a + 1) - 1) :=
    ⟨2 ^ (a + 1) + 1, -2, by ring⟩
  have h2 : IsCoprime (2 ^ (a + 1) + 1 : ℤ) (2 ^ (2 * a + 1) - 1) :=
    ⟨2 ^ (a + 1) - 1, -2, by ring⟩
  have h3 : IsCoprime (2 - 2 ^ (a + 1) : ℤ) (2 ^ (2 * a + 1) - 1) := ⟨1 + 2 ^ a, 1, by ring⟩
  have h4 : IsCoprime (1 + 2 ^ a : ℤ) (2 ^ (2 * a + 1) - 1) := ⟨2 - 2 ^ (a + 1), 1, by ring⟩
  have hunits : ((Nat.card Kˣ : ℕ) : ℤ) = 2 ^ (2 * a + 1) - 1 := by
    rw [Nat.card_units, hK, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]
  refine ⟨hchar, ⟨RingEquiv.ofBijective (iterateFrobenius K 2 (a + 1))
      (iterateFrobenius K 2 (a + 1)).injective.bijective_of_finite,
      fun x => iterateFrobenius_def (p := 2) (a + 1) x⟩, fun x => ?_, fun x => ?_,
    Int.isCoprime_iff_gcd_eq_one.mp h1, Int.isCoprime_iff_gcd_eq_one.mp h2,
    Int.isCoprime_iff_gcd_eq_one.mp h3, Int.isCoprime_iff_gcd_eq_one.mp h4, ?_,
    zpow_bijective_of_isCoprime (hunits ▸ h1), zpow_bijective_of_isCoprime (hunits ▸ h2),
    zpow_bijective_of_isCoprime (hunits ▸ h3), zpow_bijective_of_isCoprime (hunits ▸ h4)⟩
  · rw [← pow_mul, show 2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ (2 * a + 1) * 2 by ring, pow_mul, hq]
  · rw [iterate_pow_eq_pow, ← pow_mul, show (a + 1) * (2 * a + 1) = (2 * a + 1) * (a + 1) by ring,
      pow_mul]
    induction a + 1 with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_mul, ih, hq]
  · exact Int.modEq_iff_dvd.2 ⟨1, by ring⟩

end CFSG.LieType.Ree
