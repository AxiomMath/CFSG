module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDetOrders
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.SeitzReduction.F4Pilot (idxA idxBC idxD idx2D profile_idxA profile_idxBC profile_idxD
  profile_idx2D idxA_le idxBC_le idxD_le idx2D_le profile_top_eq mul_succ_eq_two_mul_div_two)

theorem two_mul_le_of_dvd_ne {k X : ℕ} (hX : 0 < X) (h : k ∣ X) (hne : k ≠ X) : 2 * k ≤ X := by
  obtain ⟨c, rfl⟩ := h
  rcases c with _ | _ | c
  · simp at hX
  · simp at hne
  · have : k * 2 ≤ k * (c + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    linarith

theorem idxBC_gap {n g k : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) (hk : idxBC n g k) :
    k = g * (2 * n) ∨ k ≤ g * (2 * (n - 1)) := by
  obtain ⟨i, hi, hd⟩ := hk
  simp only [Finset.mem_Icc] at hi
  rcases Nat.lt_or_ge i n with hin | hin
  · right
    exact (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hd).trans
      (Nat.mul_le_mul_left _ (by omega))
  · obtain rfl : i = n := by omega
    by_cases hkn : k = g * (2 * i)
    · exact Or.inl hkn
    · right
      have h2 := two_mul_le_of_dvd_ne (Nat.mul_pos (by omega) (by omega)) hd hkn
      have : g * (2 * i) ≤ 2 * (g * (2 * (i - 1))) := by
        calc g * (2 * i) ≤ g * (2 * (2 * (i - 1))) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * (g * (2 * (i - 1))) := by ring
      omega

theorem idxD_gap {n g k : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hk : idxD n g k) :
    k = g * (2 * (n - 1)) ∨ k ≤ g * (2 * (n - 2)) := by
  rcases hk with hd | ⟨i, hi, hd⟩
  · right
    exact (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hd).trans
      (Nat.mul_le_mul_left _ (by omega))
  · simp only [Finset.mem_Icc] at hi
    rcases Nat.lt_or_ge i (n - 1) with hin | hin
    · right
      exact (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hd).trans
        (Nat.mul_le_mul_left _ (by omega))
    · obtain rfl : i = n - 1 := by omega
      by_cases hkn : k = g * (2 * (n - 1))
      · exact Or.inl hkn
      · right
        have h2 := two_mul_le_of_dvd_ne (Nat.mul_pos (by omega) (by omega)) hd hkn
        have : g * (2 * (n - 1)) ≤ 2 * (g * (2 * (n - 2))) := by
          calc g * (2 * (n - 1)) ≤ g * (2 * (2 * (n - 2))) := Nat.mul_le_mul_left _ (by omega)
            _ = 2 * (g * (2 * (n - 2))) := by ring
        omega

theorem idxA_top {r f : ℕ} (hr : 1 ≤ r) : idxA r f (f * (r + 1)) :=
  ⟨r + 1, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩

theorem idxA_sub_top {r f : ℕ} (hr : 2 ≤ r) : idxA r f (f * r) :=
  ⟨r, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩

theorem two_mul_mul_tri (r f : ℕ) : 2 * (f * (r * (r + 1) / 2)) = f * (r + 1) * r := by
  have h := mul_succ_eq_two_mul_div_two r
  calc 2 * (f * (r * (r + 1) / 2)) = f * (2 * (r * (r + 1) / 2)) := by ring
    _ = f * (r * (r + 1)) := by rw [← h]
    _ = f * (r + 1) * r := by ring

theorem vsA_top {M N w r f : ℕ} {Z : ℕ → Prop} (hr : 1 ≤ r) (hf : 1 ≤ f) (h : Profile M N Z)
    (hw : Z w) (hle : ∀ k, Z k → k ≤ w) (h6 : 6 < w ∨ 6 < f * (r + 1))
    (hM : M = ordA r (2 ^ f)) :
    N = f * (r * (r + 1) / 2) ∧ w = f * (r + 1) ∧
      ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxA r f k) := by
  have hS := profile_idxA hr hf
  rw [← hM] at hS
  have hZ := (h.transfer hS).2
  rcases h6 with h6 | h6
  · obtain ⟨hN, hw'⟩ := profile_top_eq h hS hw h6 hle (idxA_top hr)
      (fun k hk => idxA_le (by omega) hk)
    exact ⟨hN, hw', hZ⟩
  · obtain ⟨hN, hw'⟩ := profile_top_eq hS h (idxA_top hr) h6 (fun k hk => idxA_le (by omega) hk)
      hw hle
    exact ⟨hN.symm, hw'.symm, hZ⟩

theorem vsA_rank {M a b e r f : ℕ} {Z : ℕ → Prop} (hr : 1 ≤ r) (hf : 1 ≤ f) (he : 1 ≤ e)
    (h : Profile M (e * a) Z) (hw : Z (e * b)) (hle : ∀ k, Z k → k ≤ e * b)
    (h6 : 6 < e * b ∨ 6 < f * (r + 1)) (hM : M = ordA r (2 ^ f)) :
    2 * a = b * r ∧ e * b = f * (r + 1) ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxA r f k) := by
  obtain ⟨hN, hw', hZ⟩ := vsA_top hr hf h hw hle h6 hM
  refine ⟨Nat.eq_of_mul_eq_mul_left (by omega : 0 < e) ?_, hw', hZ⟩
  calc e * (2 * a) = 2 * (e * a) := by ring
    _ = 2 * (f * (r * (r + 1) / 2)) := by rw [hN]
    _ = f * (r + 1) * r := two_mul_mul_tri r f
    _ = e * (b * r) := by rw [← hw']; ring

theorem vsA_two {M N r f : ℕ} {Z : ℕ → Prop} (hr : 1 ≤ r) (hf : 1 ≤ f) (h : Profile M N Z)
    (hM : M = ordA r (2 ^ f)) : N = f * (r * (r + 1) / 2) := by
  have hS := profile_idxA hr hf
  rw [← hM] at hS
  exact (h.transfer hS).1

theorem small_of_le_six {r f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) (h : f * (r + 1) ≤ 6) :
    r ≤ 5 ∧ f ≤ 2 := by
  constructor <;> nlinarith

theorem ordA_eq_ordA {s g r f : ℕ} (hs : 1 ≤ s) (hg : 1 ≤ g) (hr : 2 ≤ r) (hf : 1 ≤ f)
    (h : ordA s (2 ^ g) = ordA r (2 ^ f)) :
    (s = r ∧ g = f) ∨ (s = 3 ∧ g = 1 ∧ r = 2 ∧ f = 2) ∨ (s = 2 ∧ g = 2 ∧ r = 3 ∧ f = 1) := by
  have hX := profile_idxA hs hg
  by_cases h6 : 6 < g * (s + 1) ∨ 6 < f * (r + 1)
  · left
    obtain ⟨h1, h2, -⟩ := vsA_rank (a := s * (s + 1) / 2) (b := s + 1) (by omega) hf hg hX
      (idxA_top hs) (fun k hk => idxA_le (by omega) hk) h6 h
    have hsr : s = r := by
      refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < s + 1) ?_
      calc (s + 1) * s = s * (s + 1) := by ring
        _ = 2 * (s * (s + 1) / 2) := mul_succ_eq_two_mul_div_two s
        _ = (s + 1) * r := h1
    subst hsr
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega : 0 < s + 1) h2⟩
  · simp only [not_or, not_lt] at h6
    obtain ⟨h6a, h6b⟩ := h6
    have hN := vsA_two (by omega) hf hX h
    obtain ⟨hr5, hf2⟩ := small_of_le_six hr hf h6b
    have hs5 : s ≤ 5 := by nlinarith
    have hg3 : g ≤ 3 := by nlinarith
    interval_cases r <;> interval_cases f <;> interval_cases s <;> interval_cases g <;>
      first | omega | (revert h; decide)

theorem ordBC_ne_ordA {n g r f : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordBC n (2 ^ g) ≠ ordA r (2 ^ f) := by
  intro h
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
  · exact ordA_ne_ordBC_two (by omega) hf hg h.symm
  · exact F4Pilot.ordA_ne_ordBC_three (by omega) hf hg h.symm
  · have h8 : 6 < g * (2 * n) := by nlinarith
    obtain ⟨h1, h2, hZ⟩ := vsA_rank (a := n * n) (b := 2 * n) (by omega) hf hg
      (profile_idxBC hg) ⟨n, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩
      (fun k hk => idxBC_le (by omega) hk) (Or.inl h8) h
    have hnr : n = r := by
      refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n) ?_
      calc 2 * n * n = 2 * (n * n) := by ring
        _ = 2 * n * r := h1
    subst hnr
    have hk2 : 2 ≤ f * n := by nlinarith
    have hk6 : f * n ≠ 6 := by
      intro h6
      rcases Nat.lt_or_ge f 2 with hf1 | hf2
      · obtain rfl : f = 1 := by omega
        obtain rfl : n = 6 := by omega
        omega
      · nlinarith
    have hk := (hZ (f * n) hk2 hk6).mpr (idxA_sub_top hr)
    have hf' : f * (n + 1) = f * n + f := by ring
    rcases idxBC_gap hr hg hk with he | hle
    · omega
    · have hB : g * (2 * (n - 1)) + 2 * g = g * (2 * n) := by
        have : 2 * (n - 1) + 2 = 2 * n := by omega
        calc g * (2 * (n - 1)) + 2 * g = g * (2 * (n - 1) + 2) := by ring
          _ = g * (2 * n) := by rw [this]
      have h2g : 2 * g ≤ f := by omega
      have hC : 2 * g * (n + 1) ≤ f * (n + 1) := Nat.mul_le_mul_right _ h2g
      have hD : 2 * g * (n + 1) = g * (2 * n) + 2 * g := by ring
      omega

theorem ordD_ne_ordA {n g r f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordD n (2 ^ g) ≠ ordA r (2 ^ f) := by
  intro h
  have hX := profile_idxD (by omega : 1 ≤ n) hg
  have hw : idxD n g (g * (2 * (n - 1))) :=
    Or.inr ⟨n - 1, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩
  have hle : ∀ k, idxD n g k → k ≤ g * (2 * (n - 1)) :=
    fun k hk => idxD_le (by omega) (by omega) hk
  by_cases h6 : 6 < g * (2 * (n - 1)) ∨ 6 < f * (r + 1)
  · obtain ⟨h1, h2, hZ⟩ := vsA_rank (a := n * (n - 1)) (b := 2 * (n - 1)) (by omega) hf hg hX
      hw hle h6 h
    have hnr : n = r := by
      refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * (n - 1)) ?_
      calc 2 * (n - 1) * n = 2 * (n * (n - 1)) := by ring
        _ = 2 * (n - 1) * r := h1
    subst hnr
    have hk2 : 2 ≤ f * n := by nlinarith
    have hk6 : f * n ≠ 6 := by
      intro h6'
      rcases Nat.lt_or_ge f 2 with hf1 | hf2
      · obtain rfl : f = 1 := by omega
        obtain rfl : n = 6 := by omega
        omega
      · nlinarith
    have hk := (hZ (f * n) hk2 hk6).mpr (idxA_sub_top hr)
    have hf' : f * (n + 1) = f * n + f := by ring
    rcases idxD_gap hn hg hk with he | hle'
    · omega
    · have hB : g * (2 * (n - 2)) + 2 * g = g * (2 * (n - 1)) := by
        have : 2 * (n - 2) + 2 = 2 * (n - 1) := by omega
        calc g * (2 * (n - 2)) + 2 * g = g * (2 * (n - 2) + 2) := by ring
          _ = g * (2 * (n - 1)) := by rw [this]
      have h2g : 2 * g ≤ f := by omega
      have hC : 2 * g * (n + 1) ≤ f * (n + 1) := Nat.mul_le_mul_right _ h2g
      have hD : 2 * g * (n + 1) = g * (2 * (n - 1)) + 4 * g := by
        have : n + 1 = (n - 1) + 2 := by omega
        rw [this]; ring
      omega
  · simp only [not_or, not_lt] at h6
    obtain ⟨h6a, h6b⟩ := h6
    have hN := vsA_two (by omega) hf hX h
    obtain ⟨hr5, hf2⟩ := small_of_le_six hr hf h6b
    have h6g : g * 6 ≤ g * (2 * (n - 1)) := Nat.mul_le_mul_left _ (by omega)
    obtain rfl : g = 1 := by omega
    obtain rfl : n = 4 := by omega
    interval_cases r <;> interval_cases f <;> omega

theorem succ_le_two_pow_pred {n : ℕ} (hn : 3 ≤ n) : n + 1 ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
    omega

theorem ordTwistedD_succ_eq {r q : ℕ} (hr : 1 ≤ r) (hqe : Even q) :
    ordTwistedD (r + 1) q = q ^ (2 * (r * (r + 1) / 2)) * ((q ^ (r + 1) + 1) * ((q ^ 2 - 1) *
      ∏ i ∈ Finset.Icc 2 r, (q ^ (2 * i) - 1))) := by
  have hodd : Odd (q ^ (r + 1) + 1) := ((Nat.even_pow' (by omega)).mpr hqe).add_one
  have hexp : (r + 1) * (r + 1 - 1) = 2 * (r * (r + 1) / 2) := by
    rw [← mul_succ_eq_two_mul_div_two r, Nat.add_sub_cancel]; ring
  rw [ordTwistedD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd), Nat.div_one, hexp,
    Nat.add_sub_cancel, LocalAnalysis.ComponentInitial.LinearFlag.prod_Icc_one_eq _ hr, Nat.mul_one,
    mul_assoc]

theorem ordA_sq_mul_gcd {r q : ℕ} (hr : 1 ≤ r) :
    ordA r (q ^ 2) * Nat.gcd (r + 1) (q ^ 2 - 1) = q ^ (2 * (r * (r + 1) / 2)) *
      ((∏ i ∈ Finset.Icc 2 r, (q ^ (2 * i) - 1)) * (q ^ (2 * (r + 1)) - 1)) := by
  have hprod : ∏ i ∈ Finset.Icc 2 (r + 1), ((q ^ 2) ^ i - 1) =
      (∏ i ∈ Finset.Icc 2 r, (q ^ (2 * i) - 1)) * (q ^ (2 * (r + 1)) - 1) := by
    rw [Finset.prod_Icc_succ_top (by omega)]
    simp only [← pow_mul]
  have hdvd : Nat.gcd (r + 1) (q ^ 2 - 1) ∣
      (q ^ 2) ^ (r * (r + 1) / 2) * ∏ i ∈ Finset.Icc 2 (r + 1), ((q ^ 2) ^ i - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one (q ^ 2) (r + 1)).trans
      ((Finset.dvd_prod_of_mem (fun i => (q ^ 2) ^ i - 1) (a := r + 1)
        (by simp only [Finset.mem_Icc]; omega)).trans (dvd_mul_left _ _)))
  rw [ordA, Nat.div_mul_cancel hdvd, hprod, ← pow_mul]

theorem ordTwistedD_succ_ne_ordA_sq {r q : ℕ} (hr : 3 ≤ r) (hq : 2 ≤ q) (hqe : Even q) :
    ordTwistedD (r + 1) q ≠ ordA r (q ^ 2) := by
  intro h
  have hA := ordA_sq_mul_gcd (q := q) (by omega : 1 ≤ r)
  rw [← h, ordTwistedD_succ_eq (by omega) hqe] at hA
  have hd : Nat.gcd (r + 1) (q ^ 2 - 1) ≤ r + 1 :=
    Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  generalize Nat.gcd (r + 1) (q ^ 2 - 1) = d at hA hd
  have hPpos : 0 < ∏ i ∈ Finset.Icc 2 r, (q ^ (2 * i) - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    have : 1 < q ^ (2 * i) := Nat.one_lt_pow (by omega) (by omega)
    omega
  generalize ∏ i ∈ Finset.Icc 2 r, (q ^ (2 * i) - 1) = P at hA hPpos
  have hEpos : 0 < q ^ (2 * (r * (r + 1) / 2)) := pow_pos (by omega) _
  generalize q ^ (2 * (r * (r + 1) / 2)) = E at hA hEpos
  have hB1 : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ (by omega)
  have hsq : q ^ (2 * (r + 1)) - 1 = (q ^ (r + 1) + 1) * (q ^ (r + 1) - 1) := by
    rw [mul_comm 2, pow_mul]
    have hB2 : 1 ≤ (q ^ (r + 1)) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hB1, hB2]
    ring
  rw [hsq] at hA
  have hkey : (q ^ 2 - 1) * d = q ^ (r + 1) - 1 := by
    have hpos : 0 < E * P * (q ^ (r + 1) + 1) := Nat.mul_pos (Nat.mul_pos hEpos hPpos) (by omega)
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc E * P * (q ^ (r + 1) + 1) * ((q ^ 2 - 1) * d)
        = E * ((q ^ (r + 1) + 1) * ((q ^ 2 - 1) * P)) * d := by ring
      _ = E * (P * ((q ^ (r + 1) + 1) * (q ^ (r + 1) - 1))) := hA
      _ = E * P * (q ^ (r + 1) + 1) * (q ^ (r + 1) - 1) := by ring
  have h2r : r + 1 ≤ 2 ^ (r - 1) := succ_le_two_pow_pred hr
  have hq2 : 2 ^ (r - 1) ≤ q ^ (r - 1) := Nat.pow_le_pow_left hq _
  have hsplit : q ^ (r + 1) = q ^ 2 * q ^ (r - 1) := by
    rw [← pow_add]; congr 1; omega
  have hQ : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hbig : q ^ 2 * (r + 1) ≤ q ^ (r + 1) := by
    rw [hsplit]; exact Nat.mul_le_mul_left _ (h2r.trans hq2)
  have hdle : (q ^ 2 - 1) * d ≤ (q ^ 2 - 1) * (r + 1) := Nat.mul_le_mul_left _ hd
  have hsub : (q ^ 2 - 1) * (r + 1) + (r + 1) = q ^ 2 * (r + 1) := by
    rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega))]
  omega

theorem ordTwistedD_ne_ordA {n g r f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordTwistedD n (2 ^ g) ≠ ordA r (2 ^ f) := by
  intro h
  have hX := profile_idx2D (by omega : 1 ≤ n) hg
  have hgn : 0 < g * n := Nat.mul_pos (by omega) (by omega)
  have hw : idx2D n g (g * (2 * n)) := Or.inl ⟨⟨1, by ring⟩, fun h' => by
    have := Nat.le_of_dvd hgn h'
    nlinarith⟩
  have hle : ∀ k, idx2D n g k → k ≤ g * (2 * n) := fun k hk =>
    (idx2D_le (by omega) (by omega) hk).trans_eq (by ring)
  have h8 : 6 < g * (2 * n) := by nlinarith
  obtain ⟨h1, h2, -⟩ := vsA_rank (a := n * (n - 1)) (b := 2 * n) (by omega) hf hg hX hw hle
    (Or.inl h8) h
  have hnr : n - 1 = r := by
    refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n) ?_
    calc 2 * n * (n - 1) = 2 * (n * (n - 1)) := by ring
      _ = 2 * n * r := h1
  obtain rfl : n = r + 1 := by omega
  have hf2 : f = 2 * g := by
    refine Nat.eq_of_mul_eq_mul_right (by omega : 0 < r + 1) ?_
    calc f * (r + 1) = g * (2 * (r + 1)) := h2.symm
      _ = 2 * g * (r + 1) := by ring
  subst hf2
  rw [pow_mul'] at h
  have hq : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  exact ordTwistedD_succ_ne_ordA_sq (by omega) hq ((Nat.even_pow' (by omega)).mpr even_two) h

end CFSG.SeitzReduction.LinearPilot
