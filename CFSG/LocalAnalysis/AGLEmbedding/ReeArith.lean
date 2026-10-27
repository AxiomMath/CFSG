module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem exists_ppd_torus_element_odd {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (hodd : Odd n) {B X : Subgroup G}
    (htorus : ∃ φ : Multiplicative (GaloisField p n) ≃* X, ∀ μ : (GaloisField p n)ˣ,
      ∃ t ∈ B, ∀ a : Multiplicative (GaloisField p n),
        t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a))) :
    ∃ (r : ℕ) (t : G), r.Prime ∧ 2 * n < r ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ p ∧ ¬ r ∣ p - 1 ∧
      t ∈ B ∧ t ∈ Subgroup.normalizer (X : Set G) ∧ IsPGroup r (Subgroup.zpowers t) ∧
      (∀ x ∈ X, t ^ r * x * (t ^ r)⁻¹ = x) ∧ (∃ x ∈ X, t * x * t⁻¹ ≠ x) ∧
      ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ X →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X := by
  obtain ⟨φ, htor⟩ := htorus
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨r, hr, hrdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 hn
  have := Fact.mk hr
  have hpr : (p : ZMod r) ^ n = 1 :=
    (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos n).mp hrdvd
  have hord : orderOf (p : ZMod r) = n := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨hpr, fun k hk hk0 h => hprim k hk0 hk
      ((CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos k).mpr h)⟩
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hpr
    exact zero_ne_one hpr
  have hndvd : n ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hp0
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hndvd
    have : n ∣ 1 := ⟨c, by omega⟩
    have := Nat.le_of_dvd one_pos this
    omega
  have h2dvd : 2 ∣ r - 1 := by
    have := (hr.eq_one_or_self_of_dvd 2)
    rcases hr.eq_two_or_odd with h | h
    · exact absurd h hr2
    · omega
  have h2n : 2 * n ∣ r - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hodd) h2dvd hndvd
  have hrn2 : 2 * n < r := by
    have h := Nat.le_of_dvd (by have := hr.two_le; omega) h2n
    omega
  have hrp : r ≠ p := by
    rintro rfl
    exact hp0 (ZMod.natCast_self r)
  have hrp1 : ¬ r ∣ p - 1 := by
    have h := hprim 1 one_pos (by omega)
    rwa [pow_one] at h
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField p n)ˣ) r
    (by rw [Nat.card_units, GaloisField.card p n (by omega)]; exact hrdvd)
  have hζr : (ζ : GaloisField p n) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one, Units.val_one]
  have hμ2 : ((ζ ^ ((r + 1) / 2) : (GaloisField p n)ˣ) : GaloisField p n) ^ 2 = ζ := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.mp (hr.odd_of_ne_two hr2).add_one), pow_succ,
      hζr, one_mul]
  obtain ⟨t₀, ht₀B, ht₀⟩ := htor (ζ ^ ((r + 1) / 2))
  rw [hμ2] at ht₀
  obtain ⟨e, m, hm, hom⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t₀).ne' r hr.one_lt.ne'
  have ht := conj_pow_of_torus_conj φ ht₀ m
  have hβk : ∀ k : ℕ, ((ζ : GaloisField p n) ^ m) ^ k = 1 ↔ r ∣ k := by
    intro k
    rw [← pow_mul, ← Units.val_pow_eq_pow_val, Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one,
      hζ, hr.dvd_mul]
    exact or_iff_right hm
  have hβ0 : (ζ : GaloisField p n) ^ m ≠ 0 := by
    rw [← Units.val_pow_eq_pow_val]
    exact Units.ne_zero _
  have htr : (t₀ ^ m) ^ (r ^ e) = 1 := by rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  refine ⟨r, t₀ ^ m, hr, hrn2, hr2, by omega, hrp, hrp1, B.pow_mem ht₀B m,
    mem_normalizer_of_torus_conj φ hβ0 ht, ?_, fun x hx => ?_, ?_, fun k hk Y hYX hY => ?_⟩
  · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one htr)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hxa : (φ a : G) = x := congrArg Subtype.val ha
    rw [← hxa, conj_pow_of_torus_conj φ ht r, (hβk r).mpr dvd_rfl, one_mul, ofAdd_toAdd]
  · refine ⟨φ (Multiplicative.ofAdd 1), (φ _).2, fun h => ?_⟩
    rw [ht, toAdd_ofAdd, mul_one] at h
    have h1 := Multiplicative.ofAdd.injective (φ.injective (Subtype.ext h))
    exact hr.not_dvd_one ((hβk 1).mp (by rw [pow_one]; exact h1))
  · refine eq_bot_or_eq_of_torus_conj (by omega) hr hprim φ ?_ (fun h => hk ((hβk k).mp h))
      (conj_pow_of_torus_conj φ ht k) hYX hY
    rw [← pow_mul]
    exact (hβk (k * r)).mpr (dvd_mul_left r k)

theorem card_sylow_of_card_ree {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Nat.card L = (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1)) (S : Sylow 3 L) :
    Nat.card (S : Subgroup L) = 3 ^ (3 * n) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : 1 < 3 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
  set m := ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) with hm
  have hm0 : m ≠ 0 := Nat.mul_ne_zero (by positivity) (by omega)
  have hm3 : ¬ 3 ∣ m := by
    rw [Nat.Prime.dvd_mul Nat.prime_three]
    rintro (h | h)
    · have h1 : 3 ∣ (3 ^ n) ^ 3 := dvd_pow (dvd_pow_self 3 (by omega)) (by norm_num)
      have := (Nat.dvd_add_right h1).mp h
      omega
    · have h1 : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega)
      have h2 := Nat.dvd_sub h1 h
      rw [Nat.sub_sub_self hq1.le] at h2
      omega
  have hcard' : Nat.card L = 3 ^ (3 * n) * m := by
    rw [hcard, hm, ← pow_mul, mul_comm n 3, mul_assoc]
  rw [S.card_eq_multiplicity, hcard', Nat.factorization_mul (by positivity) hm0,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd hm3]
  simp

theorem dvd_of_ppd_dvd_card_ree {ℓ n n' : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (hℓdvd : ℓ ∣ 3 ^ (6 * n) - 1) (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ ℓ ∣ 3 ^ k - 1)
    (hℓK : ℓ ∣ (3 ^ n') ^ 3 * ((3 ^ n') ^ 3 + 1) * (3 ^ n' - 1)) : n ∣ n' := by
  have := Fact.mk hℓ
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h1 : 3 ∣ 3 ^ (6 * n) := dvd_pow_self 3 (by omega)
    have h2 := Nat.dvd_sub h1 hℓdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at h2
    omega
  have hℓq : ¬ ℓ ∣ (3 ^ n') ^ 3 := fun h =>
    hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp
      (hℓ.dvd_of_dvd_pow (hℓ.dvd_of_dvd_pow h)))
  have hℓ6 : ℓ ∣ 3 ^ (6 * n') - 1 := by
    rw [mul_assoc] at hℓK
    have h1 := (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓq) hℓK)
    have hq6 : 3 ^ (6 * n') - 1 = ((3 ^ n') ^ 3 + 1) * ((3 ^ n') ^ 3 - 1) := by
      have h6 : 3 ^ (6 * n') = ((3 ^ n') ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
      have h := Nat.sq_sub_sq ((3 ^ n') ^ 3) 1
      rw [one_pow] at h
      rw [h6, h]
    rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h2 | h2
    · rw [hq6]
      exact h2.mul_right _
    · have h3 : 3 ^ n' - 1 ∣ (3 ^ n') ^ 3 - 1 := by
        simpa using Nat.sub_dvd_pow_sub_pow (x := 3 ^ n') (y := 1) (n := 3)
      rw [hq6]
      exact (h2.trans h3).mul_left _
  have h30 : (3 : ZMod ℓ) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp this)
  have hpow : ∀ k, ℓ ∣ 3 ^ k - 1 ↔ (3 : ZMod ℓ) ^ k = 1 := fun k =>
    CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff (by norm_num) k
  have hord : orderOf (3 : ZMod ℓ) = 6 * n := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨by exact_mod_cast (hpow _).mp hℓdvd, fun k hk hk0 h =>
      hprim k hk0 hk ((hpow k).mpr (by exact_mod_cast h))⟩
  have h6 : 6 * n ∣ 6 * n' :=
    hord ▸ orderOf_dvd_of_pow_eq_one (by exact_mod_cast (hpow _).mp hℓ6)
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h6

theorem nonabelian_of_card_ree {L : Type} [Group L] [Finite L] [IsSimpleGroup L] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card L = (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1)) :
    ∃ x y : L, x * y ≠ y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcomm
  push Not at hcomm
  obtain ⟨S⟩ : Nonempty (Sylow 3 L) := inferInstance
  have hS := card_sylow_of_card_ree hn hcard S
  have hSn : (S : Subgroup L).Normal :=
    ⟨fun x hx g => by rw [hcomm g x, mul_inv_cancel_right]; exact hx⟩
  have hq1 : 1 < 3 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
  set m := ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) with hm
  have hcard' : Nat.card L = 3 ^ (3 * n) * m := by
    rw [hcard, hm, ← mul_assoc, ← pow_mul, mul_comm n 3]
  have hm2 : 2 ≤ m := by
    have h5 : 2 ≤ (3 ^ n) ^ 3 + 1 := by
      have : 1 ≤ (3 ^ n) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    calc 2 = 2 * 1 := by norm_num
      _ ≤ m := Nat.mul_le_mul h5 (by omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S : Subgroup L) with h1 | h1
  · rw [h1, Subgroup.card_bot] at hS
    have := Nat.one_lt_pow (by omega : 3 * n ≠ 0) (by norm_num : 1 < 3)
    omega
  · rw [h1, Subgroup.card_top, hcard'] at hS
    have h3 : m = 1 :=
      Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 3 ^ (3 * n)) (hS.trans (mul_one _).symm)
    omega

end CFSG.AGLEmbedding
