module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2Order
public import CFSG.HardMathSupport.Solomon.Coordinator.L514CL2

public section

namespace CFSG.HardMathSupport.Solomon.Proving


theorem cube_inj_aux (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (h : s ^ 3 + t = t ^ 3 + s) :
    s = t := by
  have hz : ((s : ℤ) - t) * ((s : ℤ) ^ 2 + s * t + t ^ 2 - 1) = 0 := by
    have h' : (s : ℤ) ^ 3 + t = (t : ℤ) ^ 3 + s := by exact_mod_cast h
    linear_combination h'
  rcases mul_eq_zero.1 hz with h1 | h1
  · omega
  · have hs' : (1 : ℤ) ≤ s := by exact_mod_cast hs
    have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
    nlinarith

theorem mixed_core (q k : ℕ) (hq3 : 3 ≤ q) (hodd : Odd q)
    (h : q ^ 3 + 2 * 2 ^ (k + 1) = 2 * (2 ^ (k + 1)) ^ 3 + q) : q = 5 ∧ k = 1 := by
  obtain ⟨a, rfl⟩ := hodd
  have ha1 : 1 ≤ a := by omega
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exfalso
    have h9 : 9 ≤ (2 * a + 1) ^ 2 := by
      have := Nat.pow_le_pow_left hq3 2
      norm_num at this
      exact this
    have key : 9 * (2 * a + 1) ≤ (2 * a + 1) ^ 3 := by
      rw [show (2 * a + 1) ^ 3 = (2 * a + 1) ^ 2 * (2 * a + 1) by ring]
      exact Nat.mul_le_mul_right _ h9
    norm_num at h
    omega
  have hQ : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have hZ : (2 * (a : ℤ) + 1) ^ 3 + 2 * 2 ^ (k + 1) = 2 * (2 ^ (k + 1)) ^ 3 + (2 * a + 1) := by
    exact_mod_cast h
  rw [hQ] at hZ
  have E1 : (a : ℤ) * (a + 1) * (2 * a + 1) = 2 ^ k * (4 * (2 ^ k) ^ 2 - 1) := by
    have h4 : 4 * ((a : ℤ) * (a + 1) * (2 * a + 1)) = 4 * (2 ^ k * (4 * (2 ^ k) ^ 2 - 1)) := by
      linear_combination hZ
    linarith
  have hdvd : (2 : ℤ) ^ k ∣ (a * (a + 1)) * (2 * a + 1) := ⟨4 * (2 ^ k) ^ 2 - 1, by rw [E1]⟩
  have hc1 : IsCoprime ((2 : ℤ) ^ k) (2 * a + 1) :=
    IsCoprime.pow_left ⟨-(a : ℤ), 1, by ring⟩
  have hH1 : (2 : ℤ) ^ k ∣ (a : ℤ) * (a + 1) := hc1.dvd_of_dvd_mul_right hdvd
  have hH2 : (2 : ℤ) ≤ 2 ^ k := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hkpos
  have hH0 : (2 : ℤ) ^ k ≠ 0 := by positivity
  have ha1' : (1 : ℤ) ≤ a := by exact_mod_cast ha1
  generalize hHdef : (2 : ℤ) ^ k = H at hH1 hH2 hH0 E1
  obtain ⟨b, hb | hb⟩ := Int.even_or_odd' (a : ℤ)
  · have hc2 : IsCoprime H ((a : ℤ) + 1) := by
      rw [← hHdef]
      exact IsCoprime.pow_left ⟨-b, 1, by linear_combination hb⟩
    have hdA : H ∣ (a : ℤ) := hc2.dvd_of_dvd_mul_right hH1
    obtain ⟨c, hc⟩ := hdA
    rw [hc] at E1
    have E2 : H * (c * (H * c + 1) * (2 * H * c + 1)) = H * (4 * H ^ 2 - 1) := by
      linear_combination E1
    have E2' := mul_left_cancel₀ hH0 E2
    have hc1' : 1 ≤ c := by
      by_contra hh
      have : c ≤ 0 := by omega
      nlinarith
    rcases (show c = 1 ∨ 2 ≤ c by omega) with rfl | hc2'
    · have hHt : H = 2 := by
        have : (H - 2) * (2 * H + 1) = 0 := by linear_combination (-1 : ℤ) * E2'
        rcases mul_eq_zero.1 this with h1 | h1
        · linarith
        · nlinarith
      have hk1 : k = 1 := by
        by_contra hne
        have hk2 : 2 ≤ k := by omega
        have h4 : (2 : ℤ) ^ 2 ≤ H := by
          rw [← hHdef]; exact pow_le_pow_right₀ (by norm_num) hk2
        norm_num at h4
        linarith
      have ha2 : (a : ℤ) = 2 := by rw [hc, hHt]; ring
      exact ⟨by omega, hk1⟩
    · exfalso
      have h4 : 2 * H ≤ c * (H * c + 1) := by nlinarith
      have h2 : 2 * H ≤ 2 * H * c + 1 := by nlinarith
      have h5 : 2 * H * (2 * H) ≤ c * (H * c + 1) * (2 * H * c + 1) :=
        mul_le_mul h4 h2 (by linarith) (by nlinarith)
      nlinarith
  · have hc2 : IsCoprime H (a : ℤ) := by
      rw [← hHdef]
      exact IsCoprime.pow_left ⟨-b, 1, by linear_combination hb⟩
    have hdB : H ∣ (a : ℤ) + 1 := hc2.dvd_of_dvd_mul_left hH1
    obtain ⟨c, hc⟩ := hdB
    have ha' : (a : ℤ) = H * c - 1 := by linarith
    rw [ha'] at E1
    have E3 : H * (c * (H * c - 1) * (2 * H * c - 1)) = H * (4 * H ^ 2 - 1) := by
      linear_combination E1
    have E3' := mul_left_cancel₀ hH0 E3
    have hc1' : 1 ≤ c := by
      by_contra hh
      have : c ≤ 0 := by omega
      nlinarith
    rcases (show c = 1 ∨ 2 ≤ c by omega) with rfl | hc2'
    · exfalso
      nlinarith
    · exfalso
      have h4 : 2 * H ≤ c * (H * c - 1) := by nlinarith
      have h2 : 2 * H ≤ 2 * H * c - 1 := by nlinarith
      have h5 : 2 * H * (2 * H) ≤ c * (H * c - 1) * (2 * H * c - 1) :=
        mul_le_mul h4 h2 (by linarith) (by nlinarith)
      nlinarith

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem typeL2_card (Y : Type) [Group Y] {r : ℕ} (h : IsTypeL2 r Y) :
    2 ≤ r ∧
    (Odd r → 2 * Nat.card (Y ⧸ Subgroup.center Y) + r = r ^ 3) ∧
    (Even r → Nat.card (Y ⧸ Subgroup.center Y) + r = r ^ 3 ∧ ∃ m, 1 ≤ m ∧ r = 2 ^ m) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hM : Nat.card (Y ⧸ Subgroup.center Y) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) := Nat.card_congr e.toEquiv
  have key := CFSG.HardMathSupport.Solomon.Coordinator.l514c_card_psl2 (F := F)
  rw [hcard, ← hM] at key
  have hr2 : 2 ≤ r := by
    rw [← hcard]
    exact Finite.one_lt_card
  have h3 : r * r ^ 2 = r ^ 3 := by ring
  have hle : r ≤ r * r ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hadd : Nat.card (Y ⧸ Subgroup.center Y) * Nat.gcd 2 (r - 1) + r = r ^ 3 := by
    rw [key, Nat.mul_sub, mul_one, h3]
    rw [h3] at hle
    omega
  refine ⟨hr2, fun hodd => ?_, fun heven => ?_⟩
  · have hg : Nat.gcd 2 (r - 1) = 2 := Nat.gcd_eq_left (by rw [Nat.odd_iff] at hodd; omega)
    rw [hg] at hadd
    omega
  · have hodd' : Odd (r - 1) := by rw [Nat.odd_iff]; rw [Nat.even_iff] at heven; omega
    have hg : Nat.gcd 2 (r - 1) = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd')
    rw [hg, mul_one] at hadd
    refine ⟨hadd, ?_⟩
    let : Fintype F := Fintype.ofFinite F
    obtain ⟨p, _, n, hp, hcardF⟩ := FiniteField.card' F
    have hr : r = p ^ (n : ℕ) := by
      rw [← hcard, Nat.card_eq_fintype_card, hcardF]
    have hp2 : p = 2 := by
      have h2 : 2 ∣ p ^ (n : ℕ) := by
        rw [← hr]
        exact even_iff_two_dvd.1 heven
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    subst hp2
    exact ⟨n, n.pos, hr⟩

theorem l2OrderUnique_holds : CFSG.HardMathSupport.Solomon.Coordinator.L2OrderUnique := by
  intro Y _ s t hs ht
  obtain ⟨hs2, hsodd, hseven⟩ := typeL2_card Y hs
  obtain ⟨ht2, htodd, hteven⟩ := typeL2_card Y ht
  rcases Nat.even_or_odd s with hse | hso <;> rcases Nat.even_or_odd t with hte | hto
  · obtain ⟨h1, -⟩ := hseven hse
    obtain ⟨h2, -⟩ := hteven hte
    exact Or.inl (cube_inj_aux s t (by omega) (by omega) (by omega))
  · obtain ⟨h1, m, hm, hsm⟩ := hseven hse
    have h2 := htodd hto
    have hkey : t ^ 3 + 2 * s = 2 * s ^ 3 + t := by omega
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hsm] at hkey
    obtain ⟨ht5, hk1⟩ := mixed_core t k (by obtain ⟨j, hj⟩ := hto; omega) hto hkey
    subst hk1
    subst ht5
    exact Or.inr (Or.inl ⟨by rw [hsm]; norm_num, rfl⟩)
  · obtain ⟨h1, m, hm, htm⟩ := hteven hte
    have h2 := hsodd hso
    have hkey : s ^ 3 + 2 * t = 2 * t ^ 3 + s := by omega
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [htm] at hkey
    obtain ⟨hs5, hk1⟩ := mixed_core s k (by obtain ⟨j, hj⟩ := hso; omega) hso hkey
    subst hk1
    subst hs5
    exact Or.inr (Or.inr ⟨rfl, by rw [htm]; norm_num⟩)
  · have h1 := hsodd hso
    have h2 := htodd hto
    exact Or.inl (cube_inj_aux s t (by omega) (by omega) (by omega))

end CFSG.HardMathSupport.Solomon.Proving
