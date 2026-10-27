module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetOrders
public import CFSG.RankThree.PartOne.S12K.OrdRigid

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.SeitzReduction.F4Pilot (idxBC idxD idx2D profile_idxBC profile_idxD profile_idx2D
  idxBC_le idxD_le idx2D_le profile_top_eq)

theorem idxBC_top {m f : ℕ} (hm : 1 ≤ m) : idxBC m f (f * (2 * m)) :=
  ⟨m, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩

theorem idxBC_of_le {m f i : ℕ} (hi : 1 ≤ i) (him : i ≤ m) : idxBC m f (f * (2 * i)) :=
  ⟨i, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩

theorem vsBC_two {M N m f : ℕ} {Z : ℕ → Prop} (hf : 1 ≤ f) (h : Profile M N Z)
    (hM : M = ordBC m (2 ^ f)) : N = f * (m * m) := by
  have hS := profile_idxBC (n := m) hf
  rw [← hM] at hS
  exact (h.transfer hS).1

theorem vsBC_top {M N w m f : ℕ} {Z : ℕ → Prop} (hm : 1 ≤ m) (hf : 1 ≤ f) (h : Profile M N Z)
    (hw : Z w) (hle : ∀ k, Z k → k ≤ w) (h6 : 6 < w ∨ 6 < f * (2 * m))
    (hM : M = ordBC m (2 ^ f)) :
    N = f * (m * m) ∧ w = f * (2 * m) ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxBC m f k) := by
  have hS := profile_idxBC (n := m) hf
  rw [← hM] at hS
  have hZ := (h.transfer hS).2
  rcases h6 with h6 | h6
  · obtain ⟨hN, hw'⟩ := profile_top_eq h hS hw h6 hle (idxBC_top hm)
      (fun k hk => idxBC_le (by omega) hk)
    exact ⟨hN, hw', hZ⟩
  · obtain ⟨hN, hw'⟩ := profile_top_eq hS h (idxBC_top hm) h6
      (fun k hk => idxBC_le (by omega) hk) hw hle
    exact ⟨hN.symm, hw'.symm, hZ⟩

theorem vsBC_rank {M a b e m f : ℕ} {Z : ℕ → Prop} (hm : 1 ≤ m) (hf : 1 ≤ f) (he : 1 ≤ e)
    (h : Profile M (e * a) Z) (hw : Z (e * b)) (hle : ∀ k, Z k → k ≤ e * b)
    (h6 : 6 < e * b ∨ 6 < f * (2 * m)) (hM : M = ordBC m (2 ^ f)) :
    2 * a = b * m ∧ e * b = f * (2 * m) ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxBC m f k) := by
  obtain ⟨hN, hw', hZ⟩ := vsBC_top hm hf h hw hle h6 hM
  refine ⟨Nat.eq_of_mul_eq_mul_left (by omega : 0 < e) ?_, hw', hZ⟩
  calc e * (2 * a) = 2 * (e * a) := by ring
    _ = 2 * (f * (m * m)) := by rw [hN]
    _ = f * (2 * m) * m := by ring
    _ = e * (b * m) := by rw [← hw']; ring

theorem ordBC_eq_ordBC {n g m f : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) (hm : 2 ≤ m) (hf : 1 ≤ f)
    (h : ordBC n (2 ^ g) = ordBC m (2 ^ f)) : n = m ∧ g = f := by
  have hX := profile_idxBC (n := n) hg
  by_cases h6 : 6 < g * (2 * n) ∨ 6 < f * (2 * m)
  · obtain ⟨h1, h2, -⟩ := vsBC_rank (a := n * n) (b := 2 * n) (by omega) hf hg hX
      (idxBC_top (by omega)) (fun k hk => idxBC_le (by omega) hk) h6 h
    have hnm : n = m := by
      refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n) ?_
      calc 2 * n * n = 2 * (n * n) := by ring
        _ = 2 * n * m := h1
    subst hnm
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) h2⟩
  · simp only [not_or, not_lt] at h6
    obtain ⟨h6a, h6b⟩ := h6
    have hN := vsBC_two hf hX h
    have hgn : g * 4 ≤ g * (2 * n) := Nat.mul_le_mul_left _ (by omega)
    have hfm : f * 4 ≤ f * (2 * m) := Nat.mul_le_mul_left _ (by omega)
    obtain rfl : g = 1 := by omega
    obtain rfl : f = 1 := by omega
    have hn3 : n ≤ 3 := by omega
    have hm3 : m ≤ 3 := by omega
    interval_cases n <;> interval_cases m <;> omega

theorem ordA_ne_ordBC {r g m f : ℕ} (hr : 1 ≤ r) (hg : 1 ≤ g) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordA r (2 ^ g) ≠ ordBC m (2 ^ f) := by
  intro h
  rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
  · exact RankThree.PartOne.S12K.ordBC_ne_ordA_one hm hf hg h.symm
  · exact LinearPilot.ordBC_ne_ordA hm hf hr2 hg h.symm

theorem ordTwistedA_ne_ordBC {u g m f : ℕ} (hu : 2 ≤ u) (hg : 1 ≤ g) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordTwistedA u (2 ^ g) ≠ ordBC m (2 ^ f) := by
  intro h
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
  · exact RankThree.PartOne.S12K.ordTwistedA_ne_ordBC_two hu hg hf h
  · exact ordBC_ne_ordTwistedA hm3 hf hu hg h.symm

theorem ordD_ne_ordBC_of_four_le {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 4 ≤ m)
    (hf : 1 ≤ f) : ordD n (2 ^ g) ≠ ordBC m (2 ^ f) := by
  intro h
  have hX := profile_idxD (by omega : 1 ≤ n) hg
  have hw : idxD n g (g * (2 * (n - 1))) :=
    Or.inr ⟨n - 1, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩
  have hle : ∀ k, idxD n g k → k ≤ g * (2 * (n - 1)) :=
    fun k hk => idxD_le (by omega) (by omega) hk
  have h8 : 6 < f * (2 * m) := by nlinarith
  obtain ⟨h1, h2, hZ⟩ := vsBC_rank (a := n * (n - 1)) (b := 2 * (n - 1)) (by omega) hf hg hX
    hw hle (Or.inr h8) h
  have hnm : n = m := by
    refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * (n - 1)) ?_
    calc 2 * (n - 1) * n = 2 * (n * (n - 1)) := by ring
      _ = 2 * (n - 1) * m := h1
  subst hnm
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 2 := ⟨n - 2, by omega⟩
  have e1 : b + 2 - 1 = b + 1 := by omega
  have e2 : b + 2 - 2 = b := by omega
  rw [e1] at h2
  have hrel : g * (b + 1) = f * (b + 2) := by linarith
  have hk2 : 2 ≤ f * (2 * (b + 1)) := by nlinarith
  have hk6 : f * (2 * (b + 1)) ≠ 6 := by
    intro h6
    have h3 : f * (b + 1) = 3 := by linarith
    have hb1 : b + 1 ≤ f * (b + 1) := Nat.le_mul_of_pos_left _ hf
    obtain rfl : b = 2 := by omega
    obtain rfl : f = 1 := by omega
    omega
  have hk := (hZ _ hk2 hk6).mpr (idxBC_of_le (m := b + 2) (by omega) (by omega : b + 1 ≤ b + 2))
  rcases LinearPilot.idxD_gap (by omega) hg hk with he | hle'
  · rw [e1] at he
    have hfg : f = g := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * (b + 1)) he
    subst hfg
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hrel
    omega
  · rw [e2] at hle'
    have h3 : f * (b + 1) ≤ g * b := by linarith
    have h4 : g * b * (b + 1) = f * (b + 2) * b := by
      rw [show g * b * (b + 1) = g * (b + 1) * b by ring, hrel]
    nlinarith [Nat.mul_le_mul_right (b + 1) h3, h4]

theorem ordD_ne_ordBC {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordD n (2 ^ g) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordD_ne_ordBC_two hn hg hf
  · exact F4Pilot.ordD_ne_ordBC_three hn hg hf
  · exact ordD_ne_ordBC_of_four_le hn hg hm4 hf

theorem ordTwistedD_ne_ordBC_of_four_le {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 4 ≤ m)
    (hf : 1 ≤ f) : ordTwistedD n (2 ^ g) ≠ ordBC m (2 ^ f) := by
  intro h
  have hX := profile_idx2D (by omega : 1 ≤ n) hg
  have hgn : 0 < g * n := Nat.mul_pos (by omega) (by omega)
  have hw : idx2D n g (g * (2 * n)) := by
    rw [show g * (2 * n) = 2 * (g * n) by ring]
    exact Or.inl ⟨dvd_rfl, fun h' => by have := Nat.le_of_dvd hgn h'; omega⟩
  have hle : ∀ k, idx2D n g k → k ≤ g * (2 * n) := fun k hk =>
    (idx2D_le (by omega) (by omega) hk).trans_eq (by ring)
  have h8 : 6 < f * (2 * m) := by nlinarith
  obtain ⟨h1, h2, hZ⟩ := vsBC_rank (a := n * (n - 1)) (b := 2 * n) (by omega) hf hg hX hw hle
    (Or.inr h8) h
  have hnm : n - 1 = m := by
    refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n) ?_
    calc 2 * n * (n - 1) = 2 * (n * (n - 1)) := by ring
      _ = 2 * n * m := h1
  obtain rfl : n = m + 1 := by omega
  have hrel : m * f = (m + 1) * g := by linarith
  have hk : idx2D (m + 1) g (g * (2 * m)) :=
    Or.inr ⟨m, by simp only [Finset.mem_Icc]; omega, dvd_rfl⟩
  have h8' : 8 ≤ g * (2 * m) := by nlinarith
  obtain ⟨i, hi, hd⟩ := (hZ _ (by omega) (by omega)).mp hk
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have h3 : 2 * m * m ∣ 2 * i * (m + 1) := dvd_of_rel (by omega : 0 < g) hrel hd
  have h4 : m * m ∣ i * (m + 1) := by
    rw [show 2 * m * m = 2 * (m * m) by ring, show 2 * i * (m + 1) = 2 * (i * (m + 1)) by ring]
      at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  have hcop1 : Nat.Coprime m (m + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)
  have h5 : m * m ∣ i := (Nat.Coprime.mul_left hcop1 hcop1).dvd_of_dvd_mul_right h4
  have h6 := Nat.le_of_dvd (by omega) h5
  nlinarith

theorem ordTwistedD_ne_ordBC {n g m f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordTwistedD n (2 ^ g) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordTwistedD_ne_ordBC_two hn hg hf
  · exact F4Pilot.ordTwistedD_ne_ordBC_three hn hg hf
  · exact ordTwistedD_ne_ordBC_of_four_le hn hg hm4 hf

end CFSG.SeitzReduction.SymplecticPilot
