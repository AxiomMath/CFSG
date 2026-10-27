module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SeitzReduction.F4Pilot (idxD idx2D profile_idxD profile_idx2D)
open CFSG.SeitzReduction.F4Pilot.EvenExc (profile_ordG2' profile_ordF4' profile_ordE6'
  profile_ordTwistedE6' profile_ordE8' profile_ordTrialityD4' profile_ordSuzuki'
  profile_ordTwistedF4')

theorem ordF4_lt_ordD_four {e : ℕ} (he : 1 ≤ e) : ordF4 (2 ^ e) < ordD 4 (2 ^ (2 * e)) := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hQ : 2 ^ (2 * e) = q ^ 2 := by rw [hq, ← pow_mul, mul_comm]
  have hodd : Odd ((q ^ 2) ^ 4 - 1) := by
    rw [← hQ]
    exact odd_pow_sub_one (by omega) (by norm_num)
  have hD : ordD 4 (q ^ 2) =
      q ^ 24 * ((q ^ 12 - 1) * (q ^ 8 - 1)) * ((q ^ 8 - 1) * (q ^ 4 - 1)) := by
    rw [ordD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd), Nat.div_one,
      show Finset.Icc 1 (4 - 1) = ({1, 2, 3} : Finset ℕ) by decide, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [← pow_mul]
    norm_num
    ring
  have hF : ordF4 q = q ^ 24 * ((q ^ 12 - 1) * (q ^ 8 - 1)) * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
    rw [ordF4]
    ring
  rw [hQ, hD, hF]
  have h1 : ∀ k, 1 ≤ k → 1 < q ^ k := fun k hk => Nat.one_lt_pow (by omega) (by omega)
  have hA : 0 < q ^ 24 * ((q ^ 12 - 1) * (q ^ 8 - 1)) := by
    have h12 := h1 12 (by norm_num)
    have h8 := h1 8 (by norm_num)
    exact Nat.mul_pos (by positivity) (Nat.mul_pos (by omega) (by omega))
  have h68 : q ^ 6 - 1 < q ^ 8 - 1 := by
    have := Nat.pow_lt_pow_right (by omega : 1 < q) (by norm_num : 6 < 8)
    have := h1 6 (by norm_num)
    omega
  have h24 : q ^ 2 - 1 < q ^ 4 - 1 := by
    have := Nat.pow_lt_pow_right (by omega : 1 < q) (by norm_num : 2 < 4)
    have := h1 2 (by norm_num)
    omega
  exact Nat.mul_lt_mul_of_pos_left (mul_lt_mul'' h68 h24 (Nat.zero_le _) (Nat.zero_le _)) hA

theorem ordG2_ne_ordD {e m f : ℕ} (he : 2 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordG2 (2 ^ e) ≠ ordD m (2 ^ f) := by
  intro h
  obtain ⟨h1, -, -⟩ := vsD_rank (a := 6) (b := 6) (by omega) hf (by omega)
    (profile_ordG2' (by omega)) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (Or.inl (by omega)) h
  omega

theorem ordF4_ne_ordD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordF4 (2 ^ e) ≠ ordD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, -⟩ := vsD_rank (a := 24) (b := 12) (by omega) hf he (profile_ordF4' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (Or.inl (by omega)) h
  obtain rfl : m = 4 := by omega
  obtain rfl : f = 2 * e := by omega
  exact (ordF4_lt_ordD_four he).ne h

theorem ordE6_ne_ordD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordE6 (2 ^ e) ≠ ordD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := vsD_rank (a := 36) (b := 12) (by omega) hf he (profile_ordE6' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (Or.inl (by omega)) h
  obtain rfl : m = 6 := by omega
  have hrel : 6 * e = 5 * f := by omega
  have hk : idxD 6 f (f * 8) := Or.inr ⟨4, by decide, by norm_num⟩
  rcases (hZ (f * 8) (by omega) (by omega)).mpr hk with h' | h' | h' | h' | h' | h' <;>
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this

theorem ordTwistedE6_ne_ordD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTwistedE6 (2 ^ e) ≠ ordD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := vsD_rank (a := 36) (b := 18) (by omega) hf he
    (profile_ordTwistedE6' he)
    (Or.inr (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩))
    (fun k hk => by
      rcases hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (Or.inl (by omega)) h
  obtain rfl : m = 4 := by omega
  obtain rfl : f = 3 * e := by omega
  rcases (hZ (e * 8) (by omega) (by omega)).mp (Or.inr (Or.inr (Or.inl dvd_rfl))) with
    hd | ⟨i, hi, hd⟩
  · have h3 : e * 8 ∣ e * 12 := by rwa [show 3 * e * 4 = e * 12 by ring] at hd
    have := Nat.dvd_of_mul_dvd_mul_left (by omega) h3
    norm_num at this
  · simp only [Finset.mem_Icc] at hi
    have h3 : e * 8 ∣ e * (6 * i) := by rwa [show 3 * e * (2 * i) = e * (6 * i) by ring] at hd
    have h8 := Nat.dvd_of_mul_dvd_mul_left (by omega) h3
    obtain ⟨hi1, hi3⟩ := hi
    interval_cases i <;> norm_num at h8

theorem ordE8_ne_ordD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordE8 (2 ^ e) ≠ ordD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := vsD_rank (a := 120) (b := 30) (by omega) hf he (profile_ordE8' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (Or.inl (by omega)) h
  obtain rfl : m = 8 := by omega
  have hrel : 15 * e = 7 * f := by omega
  rcases (hZ (f * 8) (by omega) (by omega)).mpr idxD_mid with
    h' | h' | h' | h' | h' | h' | h' | h' <;>
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this

theorem ordTrialityD4_ne_ordD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ e) ≠ ordD m (2 ^ f) := by
  intro h
  obtain ⟨h1, -, -⟩ := vsD_rank (a := 12) (b := 12) (by omega) hf he (profile_ordTrialityD4' he)
    (Or.inl ⟨dvd_rfl, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (Or.inl (by omega)) h
  omega

theorem ordSuzuki_ne_ordD {e m f : ℕ} (he : 2 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ e) ≠ ordD m (2 ^ f) := by
  intro h
  obtain ⟨h1, -, -⟩ := vsD_rank (a := 2) (b := 4) (by omega) hf (by omega)
    (profile_ordSuzuki' (by omega))
    (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (Or.inl (by omega)) h
  omega

theorem ordTwistedF4_ne_ordD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ e) ≠ ordD m (2 ^ f) := by
  intro h
  obtain ⟨h1, -, -⟩ := vsD_rank (a := 12) (b := 12) (by omega) hf he (profile_ordTwistedF4' he)
    (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (Or.inl (by omega)) h
  omega

theorem ordTits_ne_ordD {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) : ordTits ≠ ordD m (2 ^ f) := by
  rw [ordTits_eq]
  refine fun h => (profile_idxD (by omega : 1 ≤ m) hf).ne_of_ne (by decide) ?_ h.symm
  have := (twelve_le_mul_rank hm hf).1
  omega

end CFSG.SeitzReduction.OmegaPilot
