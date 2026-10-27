module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LinearAlgebra.SL2MinimalFaithfulSection

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Timmesfeld

variable {G : Type*} [Group G]

theorem card_conj_set_dvd_card_range {B N : Subgroup G} [Finite B]
    (hN : N ≤ normalizer (B : Set G)) {t : G} (ht : t ∈ B) :
    Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g} ∣
      Nat.card (SL2MinimalFaithful.conjAction hN).range := by
  set ρ := SL2MinimalFaithful.conjAction hN
  set R := ρ.range
  have himage : Subtype.val '' MulAction.orbit R (⟨t, ht⟩ : B) =
      {x | ∃ g ∈ N, x = g⁻¹ * t * g} := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨_, g, rfl⟩, rfl⟩, rfl⟩
      refine ⟨(g : G)⁻¹, N.inv_mem g.2, ?_⟩
      change ((ρ g ⟨t, ht⟩ : B) : G) = _
      rw [SL2MinimalFaithful.conjAction_apply, inv_inv]
      rfl
    · rintro ⟨g, hg, rfl⟩
      refine ⟨ρ ⟨g, hg⟩⁻¹ ⟨t, ht⟩, ⟨⟨ρ ⟨g, hg⟩⁻¹, ⟨g, hg⟩⁻¹, rfl⟩, rfl⟩, ?_⟩
      rw [map_inv, ← map_inv, SL2MinimalFaithful.conjAction_apply]
      simp
  rw [← himage, Nat.card_image_of_injective Subtype.val_injective, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem eq_or_dvd_pow_sub_one_of_dvd_card_conj_set {p d ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    {B N : Subgroup G} (hB : Nat.card B = p ^ d) (hN : N ≤ normalizer (B : Set G)) {t : G}
    (ht : t ∈ B) (hdvd : ℓ ∣ Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g}) :
    ℓ = p ∨ ∃ i, 0 < i ∧ i ≤ d ∧ ℓ ∣ p ^ i - 1 := by
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; exact (pow_pos hp.pos d).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set R := (SL2MinimalFaithful.conjAction hN).range
  have hR : ℓ ∣ Nat.card R := hdvd.trans (card_conj_set_dvd_card_range hN ht)
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' ℓ hR
  have hh1 : R.subtype h ≠ 1 := by
    intro h1
    have : h = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hh
    exact hℓ.one_lt.ne' hh.symm
  obtain ⟨e, hed, hdvd'⟩ := SL2MinimalFaithful.exists_dvd_pow_sub_pow hp hℓ R.subtype hh hh1 hB
  have hfac : p ^ d - p ^ e = p ^ e * (p ^ (d - e) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
  rw [hfac] at hdvd'
  rcases (Nat.Prime.dvd_mul hℓ).mp hdvd' with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h1))
  · exact Or.inr ⟨d - e, by omega, by omega, h1⟩

theorem not_dvd_card_conj_set_of_isPrimitivePrimeDivisor {d k ℓ : ℕ}
    (hℓ : IsPrimitivePrimeDivisor ℓ k) (hdk : d < k) {B N : Subgroup G}
    (hB : Nat.card B = 2 ^ d) (hN : N ≤ normalizer (B : Set G)) {t : G} (ht : t ∈ B) :
    ¬ ℓ ∣ Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g} := by
  intro hdvd
  have hk : 0 < k := by omega
  rcases eq_or_dvd_pow_sub_one_of_dvd_card_conj_set Nat.prime_two hℓ.prime hB hN ht hdvd with
    h2 | ⟨i, hi, hid, hdi⟩
  · exact hℓ.ne_two hk h2
  · have := Nat.le_of_dvd hi ((hℓ.dvd_sub_one_iff hk i).mp hdi)
    omega

theorem mul_pow_three_add_one (q : ℕ) :
    q * (q ^ 3 + 1) = (q + 1) * (q ^ 3 - q ^ 2 + q) := by
  have h1 : q ^ 2 ≤ q ^ 3 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · exact Nat.pow_le_pow_right hq (by norm_num)
  zify [h1]
  ring

theorem pow_five_add_one (q : ℕ) :
    q ^ 5 + 1 = (q + 1) * (q ^ 4 - q ^ 3 + q ^ 2 - q + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have h1 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have h2 : q ≤ q ^ 4 - q ^ 3 + q ^ 2 := by
    have : q ≤ q ^ 2 := by nlinarith
    omega
  zify [h1, h2]
  ring

theorem pow_three_sub_eq_one_add {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 - q ^ 2 + q = 1 + (q - 1) * (q ^ 2 + 1) := by
  have h1 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq (by norm_num)
  zify [h1, hq]
  ring

theorem pow_four_sub_eq_one_add {q : ℕ} (hq : 1 ≤ q) :
    q ^ 4 - q ^ 3 + q ^ 2 - q + 1 = 1 + (q - 1) * q * (q ^ 2 + 1) := by
  have h1 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have h2 : q ≤ q ^ 4 - q ^ 3 + q ^ 2 := by
    have : q ≤ q ^ 2 := by nlinarith
    omega
  zify [h1, h2, hq]
  ring

namespace IsPrimitivePrimeDivisor

theorem dvd_six {ℓ n : ℕ} (hℓ : IsPrimitivePrimeDivisor ℓ (6 * n)) (hn : 0 < n) :
    ℓ ∣ (2 ^ n) ^ 3 - (2 ^ n) ^ 2 + 2 ^ n := by
  have hk : 0 < 6 * n := by omega
  have h3 : ℓ ∣ 2 ^ (3 * n) + 1 :=
    (hℓ.dvd_add_one_iff hk _).mpr ⟨⟨1, by ring⟩, fun h => by
      obtain ⟨c, hc⟩ := h
      rcases c with _ | c <;> nlinarith⟩
  have h1 : ¬ ℓ ∣ 2 ^ n + 1 := by
    rw [hℓ.dvd_add_one_iff hk]
    rintro ⟨⟨c, hc⟩, -⟩
    rcases c with _ | c <;> nlinarith
  have hmul : ℓ ∣ (2 ^ n + 1) * ((2 ^ n) ^ 3 - (2 ^ n) ^ 2 + 2 ^ n) := by
    rw [← mul_pow_three_add_one, ← pow_mul, mul_comm n 3]
    exact dvd_mul_of_dvd_right h3 _
  exact (hℓ.prime.dvd_mul.mp hmul).resolve_left h1

theorem dvd_ten {ℓ n : ℕ} (hℓ : IsPrimitivePrimeDivisor ℓ (10 * n)) (hn : 0 < n) :
    ℓ ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 3 + (2 ^ n) ^ 2 - 2 ^ n + 1 := by
  have hk : 0 < 10 * n := by omega
  have h5 : ℓ ∣ 2 ^ (5 * n) + 1 :=
    (hℓ.dvd_add_one_iff hk _).mpr ⟨⟨1, by ring⟩, fun h => by
      obtain ⟨c, hc⟩ := h
      rcases c with _ | c <;> nlinarith⟩
  have h1 : ¬ ℓ ∣ 2 ^ n + 1 := by
    rw [hℓ.dvd_add_one_iff hk]
    rintro ⟨⟨c, hc⟩, -⟩
    rcases c with _ | c <;> nlinarith
  have hmul : ℓ ∣ (2 ^ n + 1) * ((2 ^ n) ^ 4 - (2 ^ n) ^ 3 + (2 ^ n) ^ 2 - 2 ^ n + 1) := by
    rw [← pow_five_add_one, ← pow_mul, mul_comm n 5]
    exact h5
  exact (hℓ.prime.dvd_mul.mp hmul).resolve_left h1

end IsPrimitivePrimeDivisor

theorem card_conj_set_ne_of_bang {n d : ℕ} (hn : 2 ≤ n) {B N : Subgroup G}
    (hB : Nat.card B = 2 ^ d) (hN : N ≤ normalizer (B : Set G)) {t : G} (ht : t ∈ B) :
    (d < 6 * n → Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g} ≠
      (2 ^ n) ^ 3 - (2 ^ n) ^ 2 + 2 ^ n) ∧
    (d < 10 * n → Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g} ≠
      (2 ^ n) ^ 4 - (2 ^ n) ^ 3 + (2 ^ n) ^ 2 - 2 ^ n + 1) := by
  refine ⟨fun hd heq => ?_, fun hd heq => ?_⟩
  · obtain ⟨ℓ, hℓ⟩ := exists_isPrimitivePrimeDivisor (k := 6 * n) (by omega) (by omega)
    exact not_dvd_card_conj_set_of_isPrimitivePrimeDivisor hℓ hd hB hN ht
      (heq ▸ IsPrimitivePrimeDivisor.dvd_six hℓ (by omega))
  · obtain ⟨ℓ, hℓ⟩ := exists_isPrimitivePrimeDivisor (k := 10 * n) (by omega) (by omega)
    exact not_dvd_card_conj_set_of_isPrimitivePrimeDivisor hℓ hd hB hN ht
      (heq ▸ IsPrimitivePrimeDivisor.dvd_ten hℓ (by omega))

theorem card_conj_set_eq_of_bang {n : ℕ} (hn : 2 ≤ n) {B N : Subgroup G}
    (hB : Nat.card B = 2 ^ (4 * n + 1)) (hN : N ≤ normalizer (B : Set G)) {t : G} (ht : t ∈ B)
    (hΩ : Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g} = (2 ^ n) ^ 3 - (2 ^ n) ^ 2 + 2 ^ n ∨
      Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g} =
        (2 ^ n) ^ 4 - (2 ^ n) ^ 3 + (2 ^ n) ^ 2 - 2 ^ n + 1 ∨
      Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g} = (2 ^ n) ^ 4) :
    Nat.card {x | ∃ g ∈ N, x = g⁻¹ * t * g} = (2 ^ n) ^ 4 := by
  obtain ⟨h6, h10⟩ := card_conj_set_ne_of_bang hn hB hN ht
  rcases hΩ with h | h | h
  · exact absurd h (h6 (by omega))
  · exact absurd h (h10 (by omega))
  · exact h

end CFSG.LocalAnalysis.EvenBN.U4
