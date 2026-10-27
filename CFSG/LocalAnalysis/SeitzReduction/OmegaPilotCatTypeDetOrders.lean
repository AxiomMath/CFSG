module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetOrders

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.SeitzReduction.F4Pilot (idxBC idxD idx2D profile_idxBC profile_idxD profile_idx2D
  idxBC_le idxD_le idx2D_le profile_top_eq)

theorem idxD_top {n f : ℕ} (hn : 2 ≤ n) : idxD n f (f * (2 * (n - 1))) :=
  Or.inr ⟨n - 1, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩

theorem idxD_mid {n f : ℕ} : idxD n f (f * n) := Or.inl dvd_rfl

theorem idx2D_top {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) : idx2D n f (f * (2 * n)) := by
  have hfn : 0 < f * n := Nat.mul_pos (by omega) (by omega)
  refine Or.inl ⟨⟨1, by ring⟩, fun h => ?_⟩
  have := Nat.le_of_dvd hfn h
  have : f * (2 * n) = 2 * (f * n) := by ring
  omega

theorem idx2D_le' {n f k : ℕ} (hf : 0 < f) (hn : 1 ≤ n) (hk : idx2D n f k) :
    k ≤ f * (2 * n) :=
  (idx2D_le hf hn hk).trans_eq (by ring)

theorem idx2D_sub_top {n f : ℕ} (hn : 2 ≤ n) : idx2D n f (f * (2 * (n - 1))) :=
  Or.inr ⟨n - 1, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩

theorem idxBC_top {n f : ℕ} (hn : 1 ≤ n) : idxBC n f (f * (2 * n)) :=
  ⟨n, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩

theorem vsD_rank {M a b e m f : ℕ} {Z : ℕ → Prop} (hm : 2 ≤ m) (hf : 1 ≤ f) (he : 1 ≤ e)
    (h : Profile M (e * a) Z) (hw : Z (e * b)) (hle : ∀ k, Z k → k ≤ e * b)
    (h6 : 6 < e * b ∨ 6 < f * (2 * (m - 1))) (hM : M = ordD m (2 ^ f)) :
    2 * a = b * m ∧ e * b = f * (2 * (m - 1)) ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxD m f k) := by
  have hS := profile_idxD (by omega : 1 ≤ m) hf
  rw [← hM] at hS
  obtain ⟨hN, hw'⟩ : e * a = f * (m * (m - 1)) ∧ e * b = f * (2 * (m - 1)) := by
    rcases h6 with h6 | h6
    · exact profile_top_eq h hS hw h6 hle (idxD_top hm) (fun k hk => idxD_le (by omega) hm hk)
    · obtain ⟨h1, h2⟩ := profile_top_eq hS h (idxD_top hm) h6
        (fun k hk => idxD_le (by omega) hm hk) hw hle
      exact ⟨h1.symm, h2.symm⟩
  refine ⟨Nat.eq_of_mul_eq_mul_left (by omega : 0 < e) ?_, hw', (h.transfer hS).2⟩
  calc e * (2 * a) = 2 * (e * a) := by ring
    _ = 2 * (f * (m * (m - 1))) := by rw [hN]
    _ = f * (2 * (m - 1)) * m := by ring
    _ = e * (b * m) := by rw [← hw']; ring

theorem vs2D_rank {M a b e m f : ℕ} {Z : ℕ → Prop} (hm : 4 ≤ m) (hf : 1 ≤ f) (he : 1 ≤ e)
    (h : Profile M (e * a) Z) (hw : Z (e * b)) (hle : ∀ k, Z k → k ≤ e * b)
    (hM : M = ordTwistedD m (2 ^ f)) :
    2 * a = b * (m - 1) ∧ e * b = f * (2 * m) ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idx2D m f k) := by
  have hS := profile_idx2D (by omega : 1 ≤ m) hf
  rw [← hM] at hS
  have h8 : 6 < f * (2 * m) := by nlinarith
  obtain ⟨hN, hw'⟩ := profile_top_eq hS h (idx2D_top (by omega) hf) h8
    (fun k hk => idx2D_le' (by omega) (by omega) hk) hw hle
  rw [eq_comm] at hN hw'
  refine ⟨Nat.eq_of_mul_eq_mul_left (by omega : 0 < e) ?_, hw', (h.transfer hS).2⟩
  calc e * (2 * a) = 2 * (e * a) := by ring
    _ = 2 * (f * (m * (m - 1))) := by rw [hN]
    _ = f * (2 * m) * (m - 1) := by ring
    _ = e * (b * (m - 1)) := by rw [← hw']; ring

theorem vsD_two {M N m f : ℕ} {Z : ℕ → Prop} (hm : 1 ≤ m) (hf : 1 ≤ f) (h : Profile M N Z)
    (hM : M = ordD m (2 ^ f)) : N = f * (m * (m - 1)) := by
  have hS := profile_idxD hm hf
  rw [← hM] at hS
  exact (h.transfer hS).1

theorem twelve_le_mul_rank {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) :
    12 ≤ f * (m * (m - 1)) ∧ (f * (m * (m - 1)) = 12 → m = 4 ∧ f = 1) := by
  have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  have h2 : m * (m - 1) ≤ f * (m * (m - 1)) := Nat.le_mul_of_pos_left _ hf
  refine ⟨by omega, fun he => ?_⟩
  have hf1 : f = 1 := by
    by_contra hc
    have : 2 * (m * (m - 1)) ≤ f * (m * (m - 1)) := Nat.mul_le_mul_right _ (by omega)
    omega
  subst hf1
  refine ⟨?_, rfl⟩
  by_contra hc
  have : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem not_dvd_succ_mul_aux {m i : ℕ} (hm : 4 ≤ m) (hi1 : 1 ≤ i) (hi : i ≤ m + 1) :
    ¬ m * (m + 1) ∣ 2 * i * (m - 1) := by
  rintro ⟨j, hj⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hj
  rcases j with _ | _ | j
  · simp only [Nat.mul_zero, Nat.mul_eq_zero] at hj
    omega
  · rcases Nat.lt_or_ge (2 * i) (m' + 4) with h | h
    · have h1 : 2 * i * m' ≤ (m' + 3) * m' := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · have h1 : (m' + 4) * m' ≤ 2 * i * m' := Nat.mul_le_mul_right _ h
      nlinarith
  · have h1 : 2 * i * m' ≤ 2 * (m' + 2) * m' := Nat.mul_le_mul_right _ (by omega)
    have h2 : (m' + 1) * (m' + 1 + 1) * 2 ≤ (m' + 1) * (m' + 1 + 1) * (j + 1 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

theorem not_dvd_sq_aux {m i : ℕ} (hm : 3 ≤ m) (hi1 : 1 ≤ i) (hi : i ≤ m) :
    ¬ m * m ∣ 2 * i * (m - 1) := by
  rintro ⟨j, hj⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hj
  rcases j with _ | _ | j
  · simp only [Nat.mul_zero, Nat.mul_eq_zero] at hj
    omega
  · rcases Nat.lt_or_ge (2 * i) (m' + 3) with h | h
    · have h1 : 2 * i * m' ≤ (m' + 2) * m' := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · have h1 : (m' + 3) * m' ≤ 2 * i * m' := Nat.mul_le_mul_right _ h
      nlinarith
  · have h1 : 2 * i * m' ≤ 2 * (m' + 1) * m' := Nat.mul_le_mul_right _ (by omega)
    have h2 : (m' + 1) * (m' + 1) * 2 ≤ (m' + 1) * (m' + 1) * (j + 1 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

theorem mul_ne_six_of_rel {m f c d g : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) (hrel : c * g = d * f)
    (h61 : m = 6 → f = 1 → c * g ≠ d) : f * m ≠ 6 := by
  intro h6
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    exact h61 (by omega) rfl (by rw [hrel, Nat.mul_one])
  · nlinarith

theorem ordD_eq_ordD {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 4 ≤ m) (hf : 1 ≤ f)
    (h : ordD n (2 ^ g) = ordD m (2 ^ f)) : n = m ∧ g = f := by
  have hX := profile_idxD (by omega : 1 ≤ n) hg
  by_cases h6 : 6 < g * (2 * (n - 1)) ∨ 6 < f * (2 * (m - 1))
  · obtain ⟨h1, h2, -⟩ := vsD_rank (a := n * (n - 1)) (b := 2 * (n - 1)) (by omega) hf hg hX
      (idxD_top (by omega)) (fun k hk => idxD_le (by omega) (by omega) hk) h6 h
    have hnm : n = m := by
      have : 2 * (n - 1) * n = 2 * (n - 1) * m := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    subst hnm
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * (n - 1)) h2⟩
  · simp only [not_or, not_lt] at h6
    obtain ⟨h6a, h6b⟩ := h6
    have ha : g * 6 ≤ g * (2 * (n - 1)) := Nat.mul_le_mul_left _ (by omega)
    have hb : f * 6 ≤ f * (2 * (m - 1)) := Nat.mul_le_mul_left _ (by omega)
    obtain rfl : g = 1 := by omega
    obtain rfl : f = 1 := by omega
    exact ⟨by omega, rfl⟩

theorem ordTwistedD_eq_ordTwistedD {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 4 ≤ m)
    (hf : 1 ≤ f) (h : ordTwistedD n (2 ^ g) = ordTwistedD m (2 ^ f)) : n = m ∧ g = f := by
  obtain ⟨h1, h2, -⟩ := vs2D_rank (a := n * (n - 1)) (b := 2 * n) hm hf hg
    (profile_idx2D (by omega : 1 ≤ n) hg) (idx2D_top (by omega) hg)
    (fun k hk => idx2D_le' (by omega) (by omega) hk) h
  have hnm : n - 1 = m - 1 := by
    have : 2 * n * (n - 1) = 2 * n * (m - 1) := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  obtain rfl : n = m := by omega
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) h2⟩

theorem ordTwistedD_ne_ordD {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTwistedD n (2 ^ g) ≠ ordD m (2 ^ f) := by
  intro h
  have h8 : 6 < g * (2 * n) := by nlinarith
  obtain ⟨h1, h2, hZ⟩ := vsD_rank (a := n * (n - 1)) (b := 2 * n) (by omega) hf hg
    (profile_idx2D (by omega : 1 ≤ n) hg) (idx2D_top (by omega) hg)
    (fun k hk => idx2D_le' (by omega) (by omega) hk) (Or.inl h8) h
  have hnm : n - 1 = m := by
    have : 2 * n * (n - 1) = 2 * n * m := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  obtain rfl : n = m + 1 := by omega
  have hrel : (m + 1) * g = (m - 1) * f := by
    have : 2 * ((m + 1) * g) = 2 * ((m - 1) * f) := by
      calc 2 * ((m + 1) * g) = g * (2 * (m + 1)) := by ring
        _ = f * (2 * (m - 1)) := h2
        _ = 2 * ((m - 1) * f) := by ring
    omega
  have hk6 : f * m ≠ 6 := mul_ne_six_of_rel hm hf hrel (fun h6 _ => by subst h6; omega)
  have hk2 : 2 ≤ f * m := by nlinarith
  rcases (hZ (f * m) hk2 hk6).mpr idxD_mid with ⟨hd, -⟩ | ⟨i, hi, hd⟩
  · have hd' : f * m ∣ g * (2 * (m + 1)) := by
      rwa [show g * (2 * (m + 1)) = 2 * (g * (m + 1)) by ring]
    have h3 : m * (m + 1) ∣ 2 * (m + 1) * (m - 1) := dvd_of_rel (by omega) hrel hd'
    have h4 : m ∣ 2 * (m - 1) := by
      have : (m + 1) * m ∣ (m + 1) * (2 * (m - 1)) := by
        rw [show (m + 1) * m = m * (m + 1) by ring,
          show (m + 1) * (2 * (m - 1)) = 2 * (m + 1) * (m - 1) by ring]
        exact h3
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) this
    obtain ⟨j, hj⟩ := h4
    rcases j with _ | _ | j
    · omega
    · omega
    · have : m * 2 ≤ m * (j + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
  · simp only [Finset.mem_Icc] at hi
    exact not_dvd_succ_mul_aux hm hi.1 (by omega) (dvd_of_rel (by omega) hrel hd)

theorem ordBC_ne_ordD {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordBC n (2 ^ g) ≠ ordD m (2 ^ f) := by
  intro h
  have h8 : 6 < g * (2 * n) := by nlinarith
  obtain ⟨h1, h2, hZ⟩ := vsD_rank (a := n * n) (b := 2 * n) (by omega) hf hg (profile_idxBC hg)
    (idxBC_top (by omega)) (fun k hk => idxBC_le (by omega) hk) (Or.inl h8) h
  have hnm : n = m := by
    have : 2 * n * n = 2 * n * m := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  subst hnm
  have hrel : n * g = (n - 1) * f := by
    have : 2 * (n * g) = 2 * ((n - 1) * f) := by
      calc 2 * (n * g) = g * (2 * n) := by ring
        _ = f * (2 * (n - 1)) := h2
        _ = 2 * ((n - 1) * f) := by ring
    omega
  have hk6 : f * n ≠ 6 := mul_ne_six_of_rel hm hf hrel (fun h6 _ => by subst h6; omega)
  have hk2 : 2 ≤ f * n := by nlinarith
  obtain ⟨i, hi, hd⟩ := (hZ (f * n) hk2 hk6).mpr idxD_mid
  simp only [Finset.mem_Icc] at hi
  exact not_dvd_sq_aux (by omega) hi.1 hi.2 (dvd_of_rel (by omega) hrel hd)

theorem ordBC_ne_ordTwistedD {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordBC n (2 ^ g) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := vs2D_rank (a := n * n) (b := 2 * n) hm hf hg (profile_idxBC hg)
    (idxBC_top (by omega)) (fun k hk => idxBC_le (by omega) hk) h
  have hnm : n = m - 1 := by
    have : 2 * n * n = 2 * n * (m - 1) := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  obtain rfl : m = n + 1 := by omega
  have hrel : g * n = f * (n + 1) := by
    have : 2 * (g * n) = 2 * (f * (n + 1)) := by
      calc 2 * (g * n) = g * (2 * n) := by ring
        _ = f * (2 * (n + 1)) := h2
        _ = 2 * (f * (n + 1)) := by ring
    omega
  have hk2 : 2 ≤ f * (2 * n) := by nlinarith
  have hk6 : f * (2 * n) ≠ 6 := by intro h6; nlinarith
  have hk : idx2D (n + 1) f (f * (2 * n)) := by
    simpa using idx2D_sub_top (n := n + 1) (f := f) (by omega)
  rcases LinearPilot.idxBC_gap (by omega) hg ((hZ _ hk2 hk6).mpr hk) with he | hle
  · have hfg : f = g := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) he
    subst hfg
    nlinarith
  ·
    have h3 : f * n ≤ g * (n - 1) := by
      have : f * (2 * n) = 2 * (f * n) := by ring
      have : g * (2 * (n - 1)) = 2 * (g * (n - 1)) := by ring
      omega
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h3
    have h4 : f * (n' + 1) * (n' + 1) ≤ g * n' * (n' + 1) := Nat.mul_le_mul_right _ h3
    have h5 : g * (n' + 1) * n' = f * (n' + 1 + 1) * n' := by rw [hrel]
    nlinarith

end CFSG.SeitzReduction.OmegaPilot
