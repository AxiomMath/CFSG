module

public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.LargeExtraspecial.A2Mod

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

namespace Ord

theorem profile_A {n : ℕ} (hn : 1 ≤ n) : Profile (ordA n 2) (n * (n + 1) / 2) (zA n 1) := by
  simpa only [pow_one, one_mul] using profile_ordA (f := 1) hn le_rfl

theorem profile_BC (n : ℕ) : Profile (ordBC n 2) (n * n) (zBC n 1) := by
  simpa only [pow_one, one_mul] using profile_ordBC (n := n) (f := 1) le_rfl

theorem profile_D {n : ℕ} (hn : 1 ≤ n) : Profile (ordD n 2) (n * (n - 1)) (zD n 1) := by
  simpa only [pow_one, one_mul] using profile_ordD (f := 1) hn le_rfl

theorem profile_2D {n : ℕ} (hn : 1 ≤ n) : Profile (ordTwistedD n 2) (n * (n - 1)) (z2D n 1) := by
  simpa only [pow_one, one_mul] using profile_ordTwistedD (f := 1) hn le_rfl

theorem two_pow_le_of_profile {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) : 2 ^ N ≤ m := by
  obtain ⟨r, hr, rfl⟩ := h.two
  exact Nat.le_mul_of_pos_right _ hr.pos

theorem ne_of_profile {m m' N N' : ℕ} {Z Z' : ℕ → Prop} (h : Profile m N Z)
    (h' : Profile m' N' Z') (hN : N ≠ N') : m ≠ m' := by
  rintro rfl
  exact hN (h.transfer h').1

theorem mul_pred_le_mul_pred {a b : ℕ} (h : a ≤ b) : a * (a - 1) ≤ b * (b - 1) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)

theorem mul_pred_ne {k a N : ℕ} (h1 : a * (a - 1) < N) (h2 : N < (a + 1) * a) :
    k * (k - 1) ≠ N := by
  intro h
  rcases le_or_gt k a with hk | hk
  · exact absurd (h ▸ mul_pred_le_mul_pred hk) (not_le.mpr h1)
  · have : (a + 1) * (a + 1 - 1) ≤ k * (k - 1) := mul_pred_le_mul_pred hk
    rw [Nat.add_sub_cancel] at this
    omega

theorem tri_ne {n a N : ℕ} (h1 : a * (a + 1) / 2 < N) (h2 : N < (a + 1) * (a + 2) / 2) :
    n * (n + 1) / 2 ≠ N := by
  intro h
  rcases le_or_gt n a with hn | hn
  · have : n * (n + 1) / 2 ≤ a * (a + 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul hn (by omega))
    omega
  · have : (a + 1) * (a + 2) / 2 ≤ n * (n + 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul hn (by omega))
    omega

theorem sq_ne {m a N : ℕ} (h1 : a * a < N) (h2 : N < (a + 1) * (a + 1)) : m * m ≠ N := by
  intro h
  rcases le_or_gt m a with hm | hm
  · exact absurd (h ▸ Nat.mul_le_mul hm hm) (not_le.mpr h1)
  · exact absurd (h ▸ Nat.mul_le_mul hm hm) (not_le.mpr h2)

theorem two_mul_tri (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

theorem bounds_of_tri_eq {n k : ℕ} (hk : 2 ≤ k) (h : n * (n + 1) / 2 = k * (k - 1)) :
    k ≤ n ∧ n + 3 ≤ 2 * k := by
  have h2 := two_mul_tri n
  rw [h] at h2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h2
  have hj : 1 ≤ j := by omega
  constructor
  · by_contra hlt
    have : n * (n + 1) ≤ j * (j + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  · by_contra hlt
    have : 2 * j * (2 * j + 1) ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

theorem ordA_two_eq (n : ℕ) :
    ordA n 2 = 2 ^ (n * (n + 1) / 2) * ∏ i ∈ Finset.Icc 2 (n + 1), (2 ^ i - 1) := by
  simp [ordA]

theorem ordD_two_eq {k : ℕ} (hk : 1 ≤ k) :
    ordD k 2 = 2 ^ (k * (k - 1)) * (2 ^ k - 1) * ∏ i ∈ Finset.Icc 1 (k - 1), (2 ^ (2 * i) - 1) := by
  have h1 : Odd (2 ^ k - 1) := odd_two_pow_sub_one (by omega)
  rw [ordD, show Nat.gcd 4 (2 ^ k - 1) = 1 from
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1), Nat.div_one]

theorem ordTwistedD_two_eq {k : ℕ} (hk : 1 ≤ k) :
    ordTwistedD k 2 =
      2 ^ (k * (k - 1)) * (2 ^ k + 1) * ∏ i ∈ Finset.Icc 1 (k - 1), (2 ^ (2 * i) - 1) := by
  have h1 : Odd (2 ^ k + 1) := ((Nat.even_pow' (by omega)).mpr even_two).add_one
  rw [ordTwistedD, show Nat.gcd 4 (2 ^ k + 1) = 1 from
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1), Nat.div_one]

theorem dvd_ordA_two {n a p : ℕ} (ha : 2 ≤ a) (han : a ≤ n + 1) (hp : p ∣ 2 ^ a - 1) :
    p ∣ ordA n 2 := by
  rw [ordA_two_eq]
  exact dvd_mul_of_dvd_right (hp.trans (Finset.dvd_prod_of_mem (fun i => 2 ^ i - 1)
    (Finset.mem_Icc.mpr ⟨ha, han⟩))) _

theorem of_dvd_ordD_two {k j p : ℕ} (hk : 1 ≤ k) (hp : IsPrimitivePrimeDivisor p j)
    (hj : 0 < j) (h : p ∣ ordD k 2) : j ∣ k ∨ ∃ i ∈ Finset.Icc 1 (k - 1), j ∣ 2 * i := by
  rw [ordD_two_eq hk] at h
  have hp2 : ¬ p ∣ 2 ^ (k * (k - 1)) := fun h2 =>
    hp.ne_two hj ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
      (hp.prime.dvd_of_dvd_pow h2))
  rcases hp.prime.dvd_mul.mp h with h | h
  · rcases hp.prime.dvd_mul.mp h with h | h
    · exact absurd h hp2
    · exact Or.inl ((hp.dvd_sub_one_iff hj k).mp h)
  · obtain ⟨i, hi, hdvd⟩ := (Nat.Prime.prime hp.prime).exists_mem_finset_dvd h
    exact Or.inr ⟨i, hi, (hp.dvd_sub_one_iff hj _).mp hdvd⟩

theorem of_dvd_ordTwistedD_two {k j p : ℕ} (hk : 1 ≤ k) (hp : IsPrimitivePrimeDivisor p j)
    (hj : 0 < j) (h : p ∣ ordTwistedD k 2) :
    (j ∣ 2 * k ∧ ¬ j ∣ k) ∨ ∃ i ∈ Finset.Icc 1 (k - 1), j ∣ 2 * i := by
  rw [ordTwistedD_two_eq hk] at h
  have hp2 : ¬ p ∣ 2 ^ (k * (k - 1)) := fun h2 =>
    hp.ne_two hj ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
      (hp.prime.dvd_of_dvd_pow h2))
  rcases hp.prime.dvd_mul.mp h with h | h
  · rcases hp.prime.dvd_mul.mp h with h | h
    · exact absurd h hp2
    · exact Or.inl ((hp.dvd_add_one_iff hj k).mp h)
  · obtain ⟨i, hi, hdvd⟩ := (Nat.Prime.prime hp.prime).exists_mem_finset_dvd h
    exact Or.inr ⟨i, hi, (hp.dvd_sub_one_iff hj _).mp hdvd⟩

theorem eq_two_mul_of_dvd {j k i : ℕ} (hjk : k ≤ j) (hi : i ∈ Finset.Icc 1 (k - 1))
    (h : j ∣ 2 * i) : j = 2 * i := by
  rw [Finset.mem_Icc] at hi
  exact (Nat.eq_of_dvd_of_lt_two_mul (by omega) h (by omega)).symm

theorem not_dvd_of_odd {j k i : ℕ} (hjk : k ≤ j) (hj : ¬ 2 ∣ j) (hi : i ∈ Finset.Icc 1 (k - 1)) :
    ¬ j ∣ 2 * i := by
  rw [Finset.mem_Icc] at hi
  intro h
  have hcop : Nat.Coprime j 2 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hj)
  have := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_left h)
  omega

theorem false_of_tri_eq {n k m : ℕ} (hn : 1 ≤ n) (hk : 4 ≤ k)
    (hN : n * (n + 1) / 2 = k * (k - 1)) (hdvd : ∀ a p, 2 ≤ a → a ≤ n + 1 → p ∣ 2 ^ a - 1 → p ∣ m)
    (hZ : ∀ j p, k ≤ j → j < 2 * k → IsPrimitivePrimeDivisor p j → p ∣ m →
      j ∣ k ∨ ∃ i ∈ Finset.Icc 1 (k - 1), j ∣ 2 * i) : False := by
  obtain ⟨hkn, hn2k⟩ := bounds_of_tri_eq (by omega) hN
  have h2 := two_mul_tri n
  rw [hN] at h2
  have h6 : n + 1 ≠ 6 := by
    intro h6
    obtain rfl : n = 5 := by omega
    exact mul_pred_ne (k := k) (a := 4) (N := 15) (by norm_num) (by norm_num) (by omega)
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := n + 1) (by omega) h6
  obtain ⟨i, hi⟩ : ∃ i, n + 1 = 2 * i := by
    rcases hZ (n + 1) p (by omega) (by omega) hp (hdvd (n + 1) p (by omega) le_rfl hp.dvd) with
      hd | ⟨i, hi, hd⟩
    · have := Nat.le_of_dvd (by omega) hd
      omega
    · exact ⟨i, eq_two_mul_of_dvd (by omega) hi hd⟩
  have hodd : ¬ 2 ∣ n := by omega
  obtain ⟨p', hp'⟩ := exists_isPrimitivePrimeDivisor (k := n) (by omega) (by omega)
  rcases hZ n p' hkn (by omega) hp' (hdvd n p' (by omega) (by omega) hp'.dvd) with
    hd | ⟨i', hi', hd⟩
  · obtain rfl : n = k := le_antisymm (Nat.le_of_dvd (by omega) hd) hkn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h2
    nlinarith
  · exact not_dvd_of_odd hkn hodd hi' hd

theorem ordA_ne_ordD {n k : ℕ} (hn : 1 ≤ n) (hk : 4 ≤ k) : ordA n 2 ≠ ordD k 2 := by
  intro h
  have hA := profile_A hn
  rw [h] at hA
  refine false_of_tri_eq (m := ordD k 2) hn hk (hA.transfer (profile_D (n := k) (by omega))).1
    (fun a p ha han hp => h ▸ dvd_ordA_two ha han hp) fun j p _ _ hp hdvd => ?_
  exact of_dvd_ordD_two (by omega) hp (by omega) hdvd

theorem ordA_ne_ordTwistedD {n k : ℕ} (hn : 1 ≤ n) (hk : 4 ≤ k) : ordA n 2 ≠ ordTwistedD k 2 := by
  intro h
  have hA := profile_A hn
  rw [h] at hA
  refine false_of_tri_eq (m := ordTwistedD k 2) hn hk
    (hA.transfer (profile_2D (n := k) (by omega))).1
    (fun a p ha han hp => h ▸ dvd_ordA_two ha han hp) fun j p hj hj2 hp hdvd => ?_
  rcases of_dvd_ordTwistedD_two (by omega) hp (by omega) hdvd with ⟨⟨c, hc⟩, hnd⟩ | h
  · exfalso
    rcases c with _ | _ | c
    · omega
    · omega
    · exact hnd ⟨1, by nlinarith⟩
  · exact Or.inr h

theorem sq_ne_mul_pred {m k : ℕ} (hm : 1 ≤ m) : m * m ≠ k * (k - 1) := by
  intro h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at h
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  rcases le_or_gt m j with hmj | hmj
  · nlinarith
  · nlinarith

theorem eq_of_mul_pred_eq {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (h : m * (m - 1) = k * (k - 1)) :
    m = k := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel] at h
  rcases lt_trichotomy a b with hab | rfl | hab
  · nlinarith
  · rfl
  · nlinarith

theorem ordBC_ne_ordD {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) : ordBC m 2 ≠ ordD k 2 :=
  ne_of_profile (profile_BC m) (profile_D hk) (sq_ne_mul_pred hm)

theorem ordBC_ne_ordTwistedD {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) : ordBC m 2 ≠ ordTwistedD k 2 :=
  ne_of_profile (profile_BC m) (profile_2D hk) (sq_ne_mul_pred hm)

theorem eq_of_ordD_eq_ordD {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (h : ordD m 2 = ordD k 2) :
    m = k := by
  have hD := profile_D hm
  rw [h] at hD
  exact eq_of_mul_pred_eq hm hk (hD.transfer (profile_D hk)).1

theorem eq_of_ordD_eq_ordTwistedD {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (h : ordD m 2 = ordTwistedD k 2) : m = k := by
  have hD := profile_D hm
  rw [h] at hD
  exact eq_of_mul_pred_eq hm hk (hD.transfer (profile_2D hk)).1

theorem eq_of_ordTwistedD_eq_ordD {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (h : ordTwistedD m 2 = ordD k 2) : m = k := by
  have hD := profile_2D hm
  rw [h] at hD
  exact eq_of_mul_pred_eq hm hk (hD.transfer (profile_D hk)).1

theorem eq_of_ordTwistedD_eq_ordTwistedD {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (h : ordTwistedD m 2 = ordTwistedD k 2) : m = k := by
  have hD := profile_2D hm
  rw [h] at hD
  exact eq_of_mul_pred_eq hm hk (hD.transfer (profile_2D hk)).1

theorem profile_F4 : Profile (ordF4 2) 24 (zF4 1) := by
  simpa only [pow_one, one_mul] using profile_ordF4 (f := 1) le_rfl

theorem profile_E6 : Profile (ordE6 2) 36 (zE6 1) := by
  simpa only [pow_one, one_mul] using profile_ordE6 (f := 1) le_rfl

theorem profile_2E6 : Profile (ordTwistedE6 2) 36 (z2E6 1) := by
  simpa only [pow_one, one_mul] using profile_ordTwistedE6 (f := 1) le_rfl

theorem profile_E7 : Profile (ordE7 2) 63 (zE7 1) := by
  simpa only [pow_one, one_mul] using profile_ordE7 (f := 1) le_rfl

theorem profile_E8 : Profile (ordE8 2) 120 (zE8 1) := by
  simpa only [pow_one, one_mul] using profile_ordE8 (f := 1) le_rfl

theorem ordTrialityD4_two : ordTrialityD4 2 = 211341312 := by decide

theorem ordD_ne_exceptional {k : ℕ} (hk : 1 ≤ k) :
    ordD k 2 ≠ ordF4 2 ∧ ordD k 2 ≠ ordE6 2 ∧ ordD k 2 ≠ ordTwistedE6 2 ∧
      ordD k 2 ≠ ordE7 2 ∧ ordD k 2 ≠ ordE8 2 := by
  have h := profile_D hk
  exact ⟨ne_of_profile h profile_F4 (mul_pred_ne (a := 5) (by norm_num) (by norm_num)),
    ne_of_profile h profile_E6 (mul_pred_ne (a := 6) (by norm_num) (by norm_num)),
    ne_of_profile h profile_2E6 (mul_pred_ne (a := 6) (by norm_num) (by norm_num)),
    ne_of_profile h profile_E7 (mul_pred_ne (a := 8) (by norm_num) (by norm_num)),
    ne_of_profile h profile_E8 (mul_pred_ne (a := 11) (by norm_num) (by norm_num))⟩

theorem ordTwistedD_ne_exceptional {k : ℕ} (hk : 1 ≤ k) :
    ordTwistedD k 2 ≠ ordF4 2 ∧ ordTwistedD k 2 ≠ ordE6 2 ∧ ordTwistedD k 2 ≠ ordTwistedE6 2 ∧
      ordTwistedD k 2 ≠ ordE7 2 ∧ ordTwistedD k 2 ≠ ordE8 2 := by
  have h := profile_2D hk
  exact ⟨ne_of_profile h profile_F4 (mul_pred_ne (a := 5) (by norm_num) (by norm_num)),
    ne_of_profile h profile_E6 (mul_pred_ne (a := 6) (by norm_num) (by norm_num)),
    ne_of_profile h profile_2E6 (mul_pred_ne (a := 6) (by norm_num) (by norm_num)),
    ne_of_profile h profile_E7 (mul_pred_ne (a := 8) (by norm_num) (by norm_num)),
    ne_of_profile h profile_E8 (mul_pred_ne (a := 11) (by norm_num) (by norm_num))⟩

theorem tri_lt_tri {a b : ℕ} (h : a < b) : a * (a + 1) / 2 < b * (b + 1) / 2 := by
  have h1 := two_mul_tri a
  have h2 := two_mul_tri b
  have : a * (a + 1) < b * (b + 1) := Nat.mul_lt_mul'' h (by omega)
  omega

theorem eq_of_tri_eq {a b : ℕ} (h : a * (a + 1) / 2 = b * (b + 1) / 2) : a = b := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact absurd h (tri_lt_tri hab).ne
  · rfl
  · exact absurd h (tri_lt_tri hab).ne'

theorem ordA_ne_exceptional {n : ℕ} (hn : 1 ≤ n) :
    ordA n 2 ≠ ordF4 2 ∧ ordA n 2 ≠ ordE6 2 ∧ ordA n 2 ≠ ordTwistedE6 2 ∧
      ordA n 2 ≠ ordE7 2 ∧ ordA n 2 ≠ ordE8 2 := by
  have h := profile_A hn
  refine ⟨ne_of_profile h profile_F4 (tri_ne (a := 6) (by norm_num) (by norm_num)), ?_, ?_,
    ne_of_profile h profile_E7 (tri_ne (a := 10) (by norm_num) (by norm_num)), ?_⟩
  · by_cases h8 : n = 8
    · subst h8
      decide
    · exact ne_of_profile h profile_E6 fun e => h8 (eq_of_tri_eq (b := 8) e)
  · by_cases h8 : n = 8
    · subst h8
      decide
    · exact ne_of_profile h profile_2E6 fun e => h8 (eq_of_tri_eq (b := 8) e)
  · by_cases h15 : n = 15
    · subst h15
      decide
    · exact ne_of_profile h profile_E8 fun e => h15 (eq_of_tri_eq (b := 15) e)

theorem ordBC_ne_exceptional (m : ℕ) :
    ordBC m 2 ≠ ordF4 2 ∧ ordBC m 2 ≠ ordE6 2 ∧ ordBC m 2 ≠ ordTwistedE6 2 ∧
      ordBC m 2 ≠ ordE7 2 ∧ ordBC m 2 ≠ ordE8 2 := by
  have h := profile_BC m
  have hsq : ∀ {a b : ℕ}, a * a = b * b → a = b := fun e => Nat.mul_self_inj.mp e
  refine ⟨ne_of_profile h profile_F4 (sq_ne (a := 4) (by norm_num) (by norm_num)), ?_, ?_,
    ne_of_profile h profile_E7 (sq_ne (a := 7) (by norm_num) (by norm_num)),
    ne_of_profile h profile_E8 (sq_ne (a := 10) (by norm_num) (by norm_num))⟩
  · by_cases h6 : m = 6
    · subst h6
      decide
    · exact ne_of_profile h profile_E6 fun e => h6 (hsq (b := 6) e)
  · by_cases h6 : m = 6
    · subst h6
      decide
    · exact ne_of_profile h profile_2E6 fun e => h6 (hsq (b := 6) e)

theorem twelve_thousand_lt_ordA {n : ℕ} (hn : 3 ≤ n) : 12096 < ordA n 2 := by
  rcases le_or_gt n 4 with h4 | h4
  · interval_cases n <;> decide
  · have h := two_pow_le_of_profile (profile_A (show 1 ≤ n by omega))
    have hT : 15 ≤ n * (n + 1) / 2 := by
      have := Nat.div_le_div_right (c := 2) (Nat.mul_le_mul (show 5 ≤ n by omega)
        (show 6 ≤ n + 1 by omega))
      simpa using this
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hT
    omega

theorem twelve_thousand_lt_ordBC {m : ℕ} (hm : 3 ≤ m) : 12096 < ordBC m 2 := by
  rcases le_or_gt m 3 with h3 | h3
  · obtain rfl : m = 3 := by omega
    decide
  · have h := two_pow_le_of_profile (profile_BC m)
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (Nat.mul_le_mul (show 4 ≤ m by omega) (show 4 ≤ m by omega))
    omega

theorem twelve_thousand_lt_ordD {k : ℕ} (hk : 4 ≤ k) : 12096 < ordD k 2 := by
  rcases le_or_gt k 4 with h4 | h4
  · obtain rfl : k = 4 := by omega
    decide
  · have h := two_pow_le_of_profile (profile_D (show 1 ≤ k by omega))
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (mul_pred_le_mul_pred (show 5 ≤ k by omega))
    norm_num at this
    omega

theorem twelve_thousand_lt_ordTwistedD {k : ℕ} (hk : 4 ≤ k) : 12096 < ordTwistedD k 2 := by
  rcases le_or_gt k 4 with h4 | h4
  · obtain rfl : k = 4 := by omega
    decide
  · have h := two_pow_le_of_profile (profile_2D (show 1 ≤ k by omega))
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (mul_pred_le_mul_pred (show 5 ≤ k by omega))
    norm_num at this
    omega

theorem twelve_thousand_lt_exceptional :
    12096 < ordF4 2 ∧ 12096 < ordE6 2 ∧ 12096 < ordTwistedE6 2 ∧ 12096 < ordE7 2 ∧
      12096 < ordE8 2 ∧ 12096 < ordTrialityD4 2 := by
  decide

end Ord

end CFSG.LargeExtraspecial.A2Mod
