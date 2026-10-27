module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.GH74.GLS.LU.Local

open CFSG.SL2MinimalFaithful CFSG.SL2MinimalFaithful.Zsigmondy

theorem pow_sub_one_dvd_iff_of_primitive {p r N : ℕ} (hr : r.Prime) (hp : 0 < p) (hN : 0 < N)
    (h1 : r ∣ p ^ N - 1) (h2 : ∀ k : ℕ, 0 < k → k < N → ¬ r ∣ p ^ k - 1) :
    (∀ m : ℕ, r ∣ p ^ m - 1 ↔ N ∣ m) ∧ N < r := by
  have := Fact.mk hr
  have hN1 : (p : ZMod r) ^ N = 1 := (dvd_pow_sub_one_iff hp N).1 h1
  have hord : orderOf (p : ZMod r) = N := by
    rw [orderOf_eq_iff hN]
    exact ⟨hN1, fun m hm hm0 hm1 => h2 m hm0 hm ((dvd_pow_sub_one_iff hp m).2 hm1)⟩
  have hiff : ∀ m : ℕ, r ∣ p ^ m - 1 ↔ N ∣ m := fun m => by
    rw [dvd_pow_sub_one_iff hp m, ← hord, orderOf_dvd_iff_pow_eq_one]
  refine ⟨hiff, ?_⟩
  have hne : (p : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN.ne'] at hN1
    exact zero_ne_one hN1
  have hdvd : N ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hne
  have h2r := hr.two_le
  have := Nat.le_of_dvd (by omega) hdvd
  omega

theorem exists_odd_prime_dvd_of_ne_two_pow {m : ℕ} (h : ∀ k : ℕ, m ≠ 2 ^ k) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ m := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd m with ⟨k, hk⟩ | ⟨r, hr, hrm, hodd⟩
  · exact absurd hk (h k)
  · exact ⟨r, hr, by rintro rfl; exact absurd hodd (by decide), hrm⟩

theorem exists_good_prime_of_three_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ((r : ℤ) ∣ ((p ^ f : ℕ) : ℤ) - ε) ∧ ¬ r ∣ f ∧
      ∀ s : ℕ, Odd s → 1 < s → s ∣ f → ¬ r ∣ p ^ (2 * (f / s)) - 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpos : 0 < p := hp.pos
  have hpf : 1 ≤ p ^ f := Nat.one_le_pow _ _ hpos
  have h2dvd : 2 ∣ p ^ 1 - 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    rw [pow_one]
    exact ⟨k, by omega⟩
  rcases hε with rfl | rfl
  · obtain ⟨r, hr, hdvd, hprim⟩ := exists_primitive_prime_dvd_pow_sub_one hp3 hf
    obtain ⟨hiff, hlt⟩ := pow_sub_one_dvd_iff_of_primitive hr hpos (by omega) hdvd hprim
    refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
    · rintro rfl
      have := Nat.le_of_dvd one_pos ((hiff 1).1 h2dvd)
      omega
    · have : ((p ^ f : ℕ) : ℤ) - 1 = ((p ^ f - 1 : ℕ) : ℤ) := by omega
      rw [this]
      exact Int.natCast_dvd_natCast.2 hdvd
    · intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    · intro s hs hs1 hsf h
      have h1 : f ∣ 2 * (f / s) := (hiff _).1 h
      have hfs : s * (f / s) = f := Nat.mul_div_cancel' hsf
      have htpos : 0 < f / s := Nat.div_pos (Nat.le_of_dvd (by omega) hsf) (by omega)
      have h3 : s * (f / s) ∣ 2 * (f / s) := by rw [hfs]; exact h1
      have h4 : s ∣ 2 := Nat.dvd_of_mul_dvd_mul_right htpos h3
      have h5 := Nat.le_of_dvd two_pos h4
      have h6 : s ≠ 2 := by
        rintro rfl
        exact absurd hs (by decide)
      omega
  · obtain ⟨r, hr, hdvd, hprim⟩ :=
      exists_primitive_prime_dvd_pow_sub_one hp3 (show 3 ≤ 2 * f by omega)
    obtain ⟨hiff, hlt⟩ := pow_sub_one_dvd_iff_of_primitive hr hpos (by omega) hdvd hprim
    have hnd : ¬ r ∣ p ^ f - 1 := fun h => by
      have := Nat.le_of_dvd (by omega) ((hiff f).1 h)
      omega
    refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
    · rintro rfl
      have := Nat.le_of_dvd one_pos ((hiff 1).1 h2dvd)
      omega
    · have hr' : Prime (r : ℤ) := Nat.prime_iff_prime_int.1 hr
      have hdvdZ : (r : ℤ) ∣ ((p : ℤ) ^ f - 1) * ((p : ℤ) ^ f + 1) := by
        have h0 : (r : ℤ) ∣ ((p ^ (2 * f) - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hdvd
        have hp2f : 1 ≤ p ^ (2 * f) := Nat.one_le_pow _ _ hpos
        have e : ((p ^ (2 * f) - 1 : ℕ) : ℤ) = ((p : ℤ) ^ f - 1) * ((p : ℤ) ^ f + 1) := by
          rw [Nat.cast_sub hp2f]
          push_cast
          ring
        rwa [e] at h0
      rcases hr'.dvd_or_dvd hdvdZ with h | h
      · exfalso
        apply hnd
        have h' : (r : ℤ) ∣ ((p ^ f - 1 : ℕ) : ℤ) := by
          have e : ((p ^ f - 1 : ℕ) : ℤ) = (p : ℤ) ^ f - 1 := by
            rw [Nat.cast_sub hpf]
            push_cast
            ring
          rwa [e]
        exact Int.natCast_dvd_natCast.1 h'
      · have e : ((p ^ f : ℕ) : ℤ) - (-1) = (p : ℤ) ^ f + 1 := by
          push_cast
          ring
        rw [e]
        exact h
    · intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    · intro s hs hs1 hsf h
      have h1 : 2 * f ∣ 2 * (f / s) := (hiff _).1 h
      have h3 : f ∣ f / s := Nat.dvd_of_mul_dvd_mul_left two_pos h1
      have htpos : 0 < f / s := Nat.div_pos (Nat.le_of_dvd (by omega) hsf) (by omega)
      have h4 := Nat.le_of_dvd htpos h3
      have h5 := Nat.div_lt_self (show 0 < f by omega) hs1
      omega

theorem exists_odd_prime_dvd_sub_of_prime {p : ℕ} (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hq : 5 ≤ p)
    (hne : ¬ (p = 5 ∧ ε = 1)) (h8 : ¬ ((p : ℤ) ≡ ε [ZMOD 8])) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ((r : ℤ) ∣ (p : ℤ) - ε) := by
  rcases hε with rfl | rfl
  · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_of_ne_two_pow (m := p - 1) (by
      intro k hk
      rcases k with _ | _ | _ | k
      · omega
      · omega
      · exact hne ⟨by omega, rfl⟩
      · apply h8
        have h8k : p - 1 = 8 * 2 ^ k := by rw [hk]; ring
        unfold Int.ModEq
        omega)
    refine ⟨r, hr, hr2, ?_⟩
    have : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by omega
    rw [this]
    exact Int.natCast_dvd_natCast.2 hrd
  · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_of_ne_two_pow (m := p + 1) (by
      intro k hk
      rcases k with _ | _ | _ | k
      · omega
      · omega
      · omega
      · apply h8
        have h8k : p + 1 = 8 * 2 ^ k := by rw [hk]; ring
        unfold Int.ModEq
        omega)
    refine ⟨r, hr, hr2, ?_⟩
    have : (p : ℤ) - -1 = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
    exact Int.natCast_dvd_natCast.2 hrd

theorem exists_odd_prime_dvd_sub_of_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hq : 5 ≤ p ^ 2) (h8 : ¬ (((p ^ 2 : ℕ) : ℤ) ≡ ε [ZMOD 8])) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ((r : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) - ε) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have hsq : p ^ 2 % 8 = 1 := by
    have h' : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases h' with h | h | h | h <;> simp [Nat.pow_mod, h]
  rcases hε with rfl | rfl
  · exfalso
    apply h8
    unfold Int.ModEq
    omega
  · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_of_ne_two_pow (m := p ^ 2 + 1) (by
      intro k hk
      rcases k with _ | _ | k
      · omega
      · omega
      · have h4k : p ^ 2 + 1 = 4 * 2 ^ k := by rw [hk]; ring
        omega)
    refine ⟨r, hr, hr2, ?_⟩
    have : ((p ^ 2 : ℕ) : ℤ) - -1 = ((p ^ 2 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
    exact Int.natCast_dvd_natCast.2 hrd

theorem exists_good_prime {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 0 < f) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hq : 5 ≤ p ^ f) (hne : ¬ (p ^ f = 5 ∧ ε = 1))
    (h8 : ¬ (((p ^ f : ℕ) : ℤ) ≡ ε [ZMOD 8])) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ((r : ℤ) ∣ ((p ^ f : ℕ) : ℤ) - ε) ∧ ¬ r ∣ f ∧
      ∀ s : ℕ, Odd s → 1 < s → s ∣ f → ¬ r ∣ p ^ (2 * (f / s)) - 1 := by
  rcases (show f = 1 ∨ f = 2 ∨ 3 ≤ f by omega) with rfl | rfl | h3
  · simp only [pow_one] at hq hne h8 ⊢
    obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_sub_of_prime ε hε hq hne h8
    refine ⟨r, hr, hr2, hrd, hr.not_dvd_one, ?_⟩
    intro s _ hs1 hsf
    have := Nat.le_of_dvd one_pos hsf
    omega
  · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_sub_of_sq hp hp2 ε hε hq h8
    refine ⟨r, hr, hr2, hrd, ?_, ?_⟩
    · intro h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
    · intro s hs hs1 hsf
      have h5 := Nat.le_of_dvd two_pos hsf
      have h6 : s ≠ 2 := by
        rintro rfl
        exact absurd hs (by decide)
      omega
  · exact exists_good_prime_of_three_le hp hp2 h3 ε hε

theorem exists_good_prime' {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 0 < f) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hq : 5 ≤ p ^ f) (hne : ¬ (p ^ f = 5 ∧ ε = 1))
    (h8 : ¬ (((p ^ f : ℕ) : ℤ) ≡ ε [ZMOD 8])) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ p ∧ ((r : ℤ) ∣ ((p ^ f : ℕ) : ℤ) - ε) ∧ ¬ r ∣ f ∧
      ∀ s : ℕ, Odd s → 1 < s → s ∣ f → ¬ r ∣ p ^ (2 * (f / s)) - 1 := by
  obtain ⟨r, hr, hr2, hrd, hrf, hs⟩ := exists_good_prime hp hp2 hf ε hε hq hne h8
  refine ⟨r, hr, hr2, ?_, hrd, hrf, hs⟩
  intro hrp
  have hpq : (r : ℤ) ∣ ((p ^ f : ℕ) : ℤ) := by
    rw [hrp, Nat.cast_pow]
    exact dvd_pow_self _ hf.ne'
  have h1 : (r : ℤ) ∣ ε := by
    have := dvd_sub hpq hrd
    rwa [sub_sub_cancel] at this
  have h2 : r ∣ 1 := by
    rcases hε with rfl | rfl
    · exact_mod_cast h1
    · have h3 : (r : ℤ) ∣ 1 := by simpa using h1
      exact_mod_cast h3
  exact hr.one_lt.ne' (Nat.dvd_one.1 h2)

end CFSG.GH74.GLS.LU.Local
