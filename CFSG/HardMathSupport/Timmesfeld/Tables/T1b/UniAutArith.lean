module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CyclicArith

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

theorem exists_pow_eq_of_mem_roots {Z : Type*} [CommGroup Z] [Finite Z] [IsCyclic Z]
    {p n m r : ℕ} (hp : p.Prime) (hM : Nat.card Z = r * m) (hr : ¬ p ∣ r)
    (hg : ¬ p ^ 2 ∣ Nat.gcd n m) {d : Z} (hd : d ^ m = 1) (hξ : ∃ ξ : Z, ξ ^ n = d)
    (hw : ∃ w : Z, w ^ m = 1 ∧ w ^ n = d ^ p) :
    ∃ c : Z, c ^ m = 1 ∧ c ^ n = d := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Z)
  have hord : orderOf γ = r * m := (orderOf_eq_card_of_forall_mem_zpowers hγ).trans hM
  have hpos : 0 < r * m := hM ▸ Nat.card_pos
  have hm0 : m ≠ 0 := fun h0 => by rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, zero_mul] at hpos; exact lt_irrefl _ hpos
  have hm0' : (m : ℤ) ≠ 0 := by exact_mod_cast hm0
  have hr0' : (r : ℤ) ≠ 0 := by exact_mod_cast hr0
  have hp0' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ d)
  obtain ⟨ξ, hξ⟩ := hξ
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ ξ)
  obtain ⟨w, hwm, hwn⟩ := hw
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ w)
  have key : ∀ i : ℤ, γ ^ i = 1 ↔ (r : ℤ) * m ∣ i := fun i => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hord]
    push_cast
    exact Iff.rfl
  have key2 : ∀ i j : ℤ, γ ^ i = γ ^ j ↔ (r : ℤ) * m ∣ i - j := fun i j => by
    rw [← key, zpow_sub, mul_inv_eq_one]
  have h1 : (r : ℤ) * m ∣ a * m := (key _).1 (by rw [zpow_mul, zpow_natCast]; exact hd)
  have h2 : (r : ℤ) * m ∣ b * n - a :=
    (key2 _ _).1 (by rw [zpow_mul, zpow_natCast]; exact hξ)
  have h3 : (r : ℤ) * m ∣ e * m := (key _).1 (by rw [zpow_mul, zpow_natCast]; exact hwm)
  have h4 : (r : ℤ) * m ∣ e * n - a * p :=
    (key2 _ _).1 (by rw [zpow_mul, zpow_natCast, zpow_mul, zpow_natCast]; exact hwn)
  obtain ⟨a', rfl⟩ : (r : ℤ) ∣ a := (mul_dvd_mul_iff_right hm0').1 h1
  obtain ⟨e', rfl⟩ : (r : ℤ) ∣ e := (mul_dvd_mul_iff_right hm0').1 h3
  have h5 : (m : ℤ) ∣ e' * n - a' * p := by
    have : (r : ℤ) * m ∣ r * (e' * n - a' * p) := by
      have e1 : (r : ℤ) * (e' * n - a' * p) = r * e' * n - r * a' * p := by ring
      rw [e1]; exact h4
    exact (mul_dvd_mul_iff_left hr0').1 this
  set G := Nat.gcd n m with hG
  have hGn : (G : ℤ) ∣ n := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left n m)
  have hGm : (G : ℤ) ∣ m := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right n m)
  have h6 : (G : ℤ) ∣ a' * p := by
    have h7 : (G : ℤ) ∣ e' * n - (e' * n - a' * p) :=
      dvd_sub (Dvd.dvd.mul_left hGn e') (hGm.trans h5)
    have e1 : e' * (n : ℤ) - (e' * n - a' * p) = a' * p := by ring
    rwa [e1] at h7
  have h8 : (G : ℤ) ∣ a' := by
    by_cases hpG : p ∣ G
    · obtain ⟨G1, hG1⟩ := hpG
      have hpG1 : ¬ p ∣ G1 := fun ⟨c, hc⟩ => hg ⟨c, by rw [hG1, hc]; ring⟩
      have hcop : IsCoprime (p : ℤ) (G1 : ℤ) :=
        Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpG1)
      have hG1a : (G1 : ℤ) ∣ a' := by
        have : (G1 : ℤ) * p ∣ a' * p := by
          have e1 : (G : ℤ) = p * G1 := by rw [hG1]; push_cast; ring
          rw [e1] at h6
          rwa [mul_comm (p : ℤ) (G1 : ℤ)] at h6
        exact (mul_dvd_mul_iff_right hp0').1 this
      have hpn : (p : ℤ) ∣ n := (Int.natCast_dvd_natCast.2 ⟨G1, hG1⟩ : (p : ℤ) ∣ G).trans hGn
      have hpm : (p : ℤ) ∣ m := (Int.natCast_dvd_natCast.2 ⟨G1, hG1⟩ : (p : ℤ) ∣ G).trans hGm
      have hpa : (p : ℤ) ∣ a' := by
        have h9 : (p : ℤ) ∣ b * n - r * a' :=
          (Dvd.dvd.mul_left hpm (r : ℤ)).trans h2
        have h10 : (p : ℤ) ∣ r * a' := by
          have := dvd_sub (Dvd.dvd.mul_left hpn b) h9
          have e1 : b * (n : ℤ) - (b * n - r * a') = r * a' := by ring
          rwa [e1] at this
        rcases hpZ.dvd_or_dvd h10 with h | h
        · exact absurd (Int.natCast_dvd_natCast.1 h) hr
        · exact h
      have : (G : ℤ) = p * G1 := by rw [hG1]; push_cast; ring
      rw [this]
      exact hcop.mul_dvd hpa hG1a
    · have hcop : IsCoprime (G : ℤ) (p : ℤ) :=
        Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpG).symm
      exact hcop.dvd_of_dvd_mul_right h6
  obtain ⟨t, ht⟩ := h8
  have hbez : (G : ℤ) = n * Nat.gcdA n m + m * Nat.gcdB n m := Nat.gcd_eq_gcd_ab n m
  refine ⟨γ ^ ((r : ℤ) * (Nat.gcdA n m * t)), ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul, key]
    exact ⟨Nat.gcdA n m * t, by ring⟩
  · rw [← zpow_natCast, ← zpow_mul, key2]
    refine ⟨-(Nat.gcdB n m * t), ?_⟩
    have : (r : ℤ) * (Nat.gcdA n m * t) * n - r * a' = r * (n * Nat.gcdA n m * t - a') := by ring
    rw [this, ht, hbez]
    ring

theorem not_dvd_pred_of_dvd_succ {p q : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) (hq : 1 ≤ q)
    (h : p ∣ q + 1) : ¬ p ∣ q - 1 := by
  intro h'
  have h2 : p ∣ 2 := by
    have := Nat.dvd_sub h h'
    have e : q + 1 - (q - 1) = 2 := by omega
    rwa [e] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem not_sq_dvd_gcd_sq_sub_one {p q n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hpq : p ∣ q + 1) (hg : ¬ p ^ 2 ∣ Nat.gcd n (q + 1)) :
    ¬ p ^ 2 ∣ Nat.gcd n (q ^ 2 - 1) := by
  intro h
  apply hg
  have hn : p ^ 2 ∣ n := h.trans (Nat.gcd_dvd_left _ _)
  have hM : p ^ 2 ∣ (q + 1) * (q - 1) := by
    have := h.trans (Nat.gcd_dvd_right _ _)
    have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      zify [Nat.one_le_pow 2 q (by omega), hq]
      ring
    rwa [e] at this
  have hc : Nat.Coprime (p ^ 2) (q - 1) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_pred_of_dvd_succ hp2 hp hq hpq))
  exact Nat.dvd_gcd hn (hc.dvd_of_dvd_mul_right hM)

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
