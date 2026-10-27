module

public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

@[expose] def idxA (n f k : ℕ) : Prop := ∃ i ∈ Finset.Icc 2 (n + 1), k ∣ f * i

@[expose] def idxBC (n f k : ℕ) : Prop := ∃ i ∈ Finset.Icc 1 n, k ∣ f * (2 * i)

@[expose] def idxD (n f k : ℕ) : Prop := k ∣ f * n ∨ ∃ i ∈ Finset.Icc 1 (n - 1), k ∣ f * (2 * i)

@[expose] def idx2D (n f k : ℕ) : Prop :=
  (k ∣ 2 * (f * n) ∧ ¬ k ∣ f * n) ∨ ∃ i ∈ Finset.Icc 1 (n - 1), k ∣ f * (2 * i)

theorem profile_idxA {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    Profile (ordA n (2 ^ f)) (f * (n * (n + 1) / 2)) (idxA n f) := by
  have hP : Odd (∏ i ∈ Finset.Icc 2 (n + 1), ((2 ^ f) ^ i - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have hZ : ∀ p k, IsPrimitivePrimeDivisor p k → 0 < k →
      (p ∣ ∏ i ∈ Finset.Icc 2 (n + 1), ((2 ^ f) ^ i - 1) ↔ idxA n f k) := by
    intro p k hp hk
    rw [(Nat.Prime.prime hp.prime).dvd_finsetProd_iff]
    exact exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f i
  have hm : ordA n (2 ^ f) = 2 ^ (f * (n * (n + 1) / 2)) *
      (∏ i ∈ Finset.Icc 2 (n + 1), ((2 ^ f) ^ i - 1)) / Nat.gcd (n + 1) (2 ^ f - 1) := by
    rw [ordA, pow_mul]
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    refine Profile.of_div hm hP (c := 1) ?_ (by simp) (by norm_num) hZ
    rw [show (1 + 1 : ℕ) = 2 by rfl, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf)]
  · refine Profile.of_div hm hP (Nat.gcd_dvd_right _ _) ?_ (Nat.gcd_pos_of_pos_left _ (by omega))
      hZ
    have h23 : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (n + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]; omega
    have := Finset.prod_dvd_prod_of_subset _ _ (fun i => (2 ^ f) ^ i - 1) h23
    rw [Finset.prod_pair (by norm_num)] at this
    exact (mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one _ 2) (Nat.sub_one_dvd_pow_sub_one _ 3)).trans
      this

theorem profile_idxBC {n f : ℕ} (hf : 1 ≤ f) :
    Profile (ordBC n (2 ^ f)) (f * (n * n)) (idxBC n f) := by
  have hP : Odd (∏ i ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * i) - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have hm : ordBC n (2 ^ f) = 2 ^ (f * (n * n)) * ∏ i ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * i) - 1) :=
    by rw [ordBC, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf), Nat.div_one,
      pow_mul 2 f (n * n)]
  refine Profile.of_eq hm hP (fun p k hp hk => ?_)
  rw [(Nat.Prime.prime hp.prime).dvd_finsetProd_iff]
  exact exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f _

theorem profile_idxD {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    Profile (ordD n (2 ^ f)) (f * (n * (n - 1))) (idxD n f) := by
  have hP : Odd (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have h1 : Odd ((2 ^ f) ^ n - 1) := odd_pow_sub_one hf hn
  have hm : ordD n (2 ^ f) = 2 ^ (f * (n * (n - 1))) *
      (((2 ^ f) ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) := by
    rw [ordD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1), Nat.div_one,
      pow_mul 2 f (n * (n - 1)), mul_assoc]
  refine Profile.of_eq hm (h1.mul hP) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, (Nat.Prime.prime hp.prime).dvd_finsetProd_iff,
    PrimDiv.dvd_pow_sub_one_iff hp hk]
  exact or_congr_right
    (exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f _)

theorem profile_idx2D {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    Profile (ordTwistedD n (2 ^ f)) (f * (n * (n - 1))) (idx2D n f) := by
  have hP : Odd (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have h1 : Odd ((2 ^ f) ^ n + 1) := odd_pow_add_one hf hn
  have hm : ordTwistedD n (2 ^ f) = 2 ^ (f * (n * (n - 1))) *
      (((2 ^ f) ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) := by
    rw [ordTwistedD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1), Nat.div_one,
      pow_mul 2 f (n * (n - 1)), mul_assoc]
  refine Profile.of_eq hm (h1.mul hP) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, (Nat.Prime.prime hp.prime).dvd_finsetProd_iff,
    PrimDiv.dvd_pow_add_one_iff hp hk]
  exact or_congr_right
    (exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f _)

theorem idxA_le {n f k : ℕ} (hf : 0 < f) (hk : idxA n f k) : k ≤ f * (n + 1) := by
  obtain ⟨i, hi, h⟩ := hk
  simp only [Finset.mem_Icc] at hi
  exact (Nat.le_of_dvd (Nat.mul_pos hf (by omega)) h).trans (Nat.mul_le_mul_left _ hi.2)

theorem idxBC_le {n f k : ℕ} (hf : 0 < f) (hk : idxBC n f k) : k ≤ f * (2 * n) := by
  obtain ⟨i, hi, h⟩ := hk
  simp only [Finset.mem_Icc] at hi
  exact (Nat.le_of_dvd (Nat.mul_pos hf (by omega)) h).trans (Nat.mul_le_mul_left _ (by omega))

theorem idxD_le {n f k : ℕ} (hf : 0 < f) (hn : 2 ≤ n) (hk : idxD n f k) :
    k ≤ f * (2 * (n - 1)) := by
  rcases hk with h | ⟨i, hi, h⟩
  · exact (Nat.le_of_dvd (Nat.mul_pos hf (by omega)) h).trans (Nat.mul_le_mul_left _ (by omega))
  · simp only [Finset.mem_Icc] at hi
    exact (Nat.le_of_dvd (Nat.mul_pos hf (by omega)) h).trans (Nat.mul_le_mul_left _ (by omega))

theorem idx2D_le {n f k : ℕ} (hf : 0 < f) (hn : 1 ≤ n) (hk : idx2D n f k) :
    k ≤ 2 * (f * n) := by
  rcases hk with ⟨h, -⟩ | ⟨i, hi, h⟩
  · exact Nat.le_of_dvd (by positivity) h
  · simp only [Finset.mem_Icc] at hi
    have := (Nat.le_of_dvd (Nat.mul_pos hf (by omega)) h).trans
      (Nat.mul_le_mul_left f (by omega : 2 * i ≤ 2 * n))
    linarith

theorem profile_top_eq {m N N' w w' : ℕ} {Z Z' : ℕ → Prop} (h : Profile m N Z)
    (h' : Profile m N' Z') (hw : Z w) (hw6 : 6 < w) (hle : ∀ k, Z k → k ≤ w) (hw' : Z' w')
    (hle' : ∀ k, Z' k → k ≤ w') : N = N' ∧ w = w' := by
  obtain ⟨hN, hZ⟩ := h.transfer h'
  have h1 : w ≤ w' := hle' w ((hZ w (by omega) (by omega)).mp hw)
  exact ⟨hN, le_antisymm h1 (hle w' ((hZ w' (by omega) (by omega)).mpr hw'))⟩

theorem mul_succ_eq_two_mul_div_two (n : ℕ) : n * (n + 1) = 2 * (n * (n + 1) / 2) :=
  (Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd).symm

theorem profile_sp6 {f : ℕ} (hf : 1 ≤ f) : Profile (ordBC 3 (2 ^ f)) (f * 9) (idxBC 3 f) :=
  profile_idxBC (n := 3) hf

theorem sp6_top {m N w f : ℕ} {Z : ℕ → Prop} (hf : 2 ≤ f) (h : Profile m N Z) (hw : Z w)
    (hle : ∀ k, Z k → k ≤ w) (hm : m = ordBC 3 (2 ^ f)) :
    N = f * 9 ∧ w = f * 6 ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxBC 3 f k) := by
  have hS := profile_sp6 (by omega : 1 ≤ f)
  rw [← hm] at hS
  obtain ⟨hN, hw'⟩ := profile_top_eq hS h (w := f * (2 * 3)) ⟨3, by simp, dvd_rfl⟩ (by omega)
    (fun k hk => idxBC_le (by omega) hk) hw hle
  exact ⟨hN.symm, by omega, fun k hk h6 => ((hS.transfer h).2 k hk h6).symm⟩

theorem sp6_one {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hm : m = ordBC 3 (2 ^ 1)) :
    N = 9 ∧ Z 4 := by
  have hS := profile_sp6 (le_refl 1)
  rw [← hm] at hS
  obtain ⟨hN, hZ⟩ := hS.transfer h
  exact ⟨by omega, (hZ 4 (by norm_num) (by norm_num)).mp ⟨2, by simp, by norm_num⟩⟩

theorem ordA_ne_ordBC_three {m g f : ℕ} (hm : 1 ≤ m) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordA m (2 ^ g) ≠ ordBC 3 (2 ^ f) := by
  intro he
  have hX := profile_idxA hm hg
  have hT := mul_succ_eq_two_mul_div_two m
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    obtain ⟨hN, h4⟩ := sp6_one hX he
    have hm3 : m ≤ 3 := by
      by_contra hc
      have h1 : 4 * 5 ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
      have h2 : m * (m + 1) / 2 ≤ g * (m * (m + 1) / 2) := Nat.le_mul_of_pos_left _ hg
      omega
    interval_cases m
    · obtain rfl : g = 9 := by simpa using hN
      revert h4; simp only [idxA]; decide
    · obtain rfl : g = 3 := by norm_num at hN; omega
      revert h4; simp only [idxA]; decide
    · norm_num at hN; omega
  · obtain ⟨hN, hw, hZ⟩ := sp6_top hf2 hX ⟨m + 1, by simp; omega, dvd_rfl⟩
      (fun k hk => idxA_le (by omega) hk) he
    generalize m * (m + 1) / 2 = T at hT hN
    have e1 : g * (m + 1) * m = g * (m + 1) * 3 := by
      calc g * (m + 1) * m = g * (m * (m + 1)) := by ring
        _ = 2 * (g * T) := by rw [hT]; ring
        _ = g * (m + 1) * 3 := by rw [hN, hw]; ring
    obtain rfl : m = 3 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
    have hrel : 3 * f = 2 * g := by omega
    have hk : idxA 3 g (g * 3) := ⟨3, by simp, dvd_rfl⟩
    obtain ⟨i, hi, hd⟩ := (hZ _ (by omega) (by omega)).mp hk
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    have := dvd_of_rel (by omega) hrel hd
    interval_cases i <;> omega

theorem ordBC_eq_ordBC_three {n g f : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f)
    (he : ordBC n (2 ^ g) = ordBC 3 (2 ^ f)) : n = 3 ∧ g = f := by
  have hX := profile_idxBC (n := n) hg
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    obtain ⟨hN, -⟩ := sp6_one hX he
    have hn3 : n ≤ 3 := by
      by_contra hc
      have h1 : 4 * 4 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
      have h2 : n * n ≤ g * (n * n) := Nat.le_mul_of_pos_left _ hg
      omega
    interval_cases n
    · omega
    · exact ⟨rfl, by omega⟩
  · obtain ⟨hN, hw, -⟩ := sp6_top hf2 hX ⟨n, by simp; omega, dvd_rfl⟩
      (fun k hk => idxBC_le (by omega) hk) he
    have h1 : g * n = f * 3 := by
      have : g * (2 * n) = 2 * (g * n) := by ring
      omega
    have e1 : g * n * n = g * n * 3 := by
      calc g * n * n = g * (n * n) := by ring
        _ = g * n * 3 := by rw [hN, h1]; ring
    obtain rfl : n = 3 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
    exact ⟨rfl, by omega⟩

theorem ordD_ne_ordBC_three {n g f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordD n (2 ^ g) ≠ ordBC 3 (2 ^ f) := by
  intro he
  have hX := profile_idxD (by omega : 1 ≤ n) hg
  have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    obtain ⟨hN, -⟩ := sp6_one hX he
    have : n * (n - 1) ≤ g * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hg
    omega
  · obtain ⟨hN, hw, -⟩ := sp6_top hf2 hX (Or.inr ⟨n - 1, by simp; omega, dvd_rfl⟩)
      (fun k hk => idxD_le (by omega) (by omega) hk) he
    have h1 : g * (n - 1) = f * 3 := by
      have : g * (2 * (n - 1)) = 2 * (g * (n - 1)) := by ring
      omega
    have e1 : g * (n - 1) * n = g * (n - 1) * 3 := by
      calc g * (n - 1) * n = g * (n * (n - 1)) := by ring
        _ = g * (n - 1) * 3 := by rw [hN, h1]; ring
    have := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
    omega

theorem ordTwistedD_ne_ordBC_three {n g f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedD n (2 ^ g) ≠ ordBC 3 (2 ^ f) := by
  intro he
  have hX := profile_idx2D (by omega : 1 ≤ n) hg
  have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    obtain ⟨hN, -⟩ := sp6_one hX he
    have : n * (n - 1) ≤ g * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hg
    omega
  · have hgn : 0 < g * n := Nat.mul_pos (by omega) (by omega)
    obtain ⟨hN, hw, hZ⟩ := sp6_top hf2 hX
      (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd hgn h; omega⟩)
      (fun k hk => idx2D_le (by omega) (by omega) hk) he
    have h1 : g * n = f * 3 := by omega
    have e1 : g * n * (n - 1) = g * n * 3 := by
      calc g * n * (n - 1) = g * (n * (n - 1)) := by ring
        _ = g * n * 3 := by rw [hN, h1]; ring
    have hn4 : n - 1 = 3 := Nat.eq_of_mul_eq_mul_left hgn e1
    obtain rfl : n = 4 := by omega
    have hrel : 3 * f = 4 * g := by omega
    have hk : idx2D 4 g (g * (2 * 3)) := Or.inr ⟨3, by simp, dvd_rfl⟩
    obtain ⟨i, hi, hd⟩ := (hZ _ (by omega) (by omega)).mp hk
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    have := dvd_of_rel (by omega) hrel hd
    interval_cases i <;> omega

theorem ordTwistedA_ne_ordBC_three {u g f : ℕ} (hu : 2 ≤ u) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedA u (2 ^ g) ≠ ordBC 3 (2 ^ f) :=
  fun h => ordBC_ne_ordTwistedA le_rfl hf hu hg h.symm

theorem profile_l6 {f : ℕ} (hf : 1 ≤ f) : Profile (ordA 5 (2 ^ f)) (f * 15) (idxA 5 f) :=
  profile_idxA (n := 5) (by norm_num) hf

theorem l6_top {m N w f : ℕ} {Z : ℕ → Prop} (hf : 2 ≤ f) (h : Profile m N Z) (hw : Z w)
    (hle : ∀ k, Z k → k ≤ w) (hm : m = ordA 5 (2 ^ f)) :
    N = f * 15 ∧ w = f * 6 ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxA 5 f k) := by
  have hS := profile_l6 (by omega : 1 ≤ f)
  rw [← hm] at hS
  obtain ⟨hN, hw'⟩ := profile_top_eq hS h (w := f * (5 + 1)) ⟨5 + 1, by simp, dvd_rfl⟩
    (by omega) (fun k hk => idxA_le (by omega) hk) hw hle
  exact ⟨hN.symm, by omega, fun k hk h6 => ((hS.transfer h).2 k hk h6).symm⟩

theorem l6_one {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hm : m = ordA 5 (2 ^ 1)) :
    N = 15 ∧ Z 4 := by
  have hS := profile_l6 (le_refl 1)
  rw [← hm] at hS
  obtain ⟨hN, hZ⟩ := hS.transfer h
  exact ⟨by omega, (hZ 4 (by norm_num) (by norm_num)).mp ⟨4, by simp, by norm_num⟩⟩

theorem ne_ordA_five_of_profile {m N w f : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hw : Z w)
    (hle : ∀ k, Z k → k ≤ w) (hf : 1 ≤ f) (h15 : N ≠ 15)
    (htop : ∀ e, 2 ≤ e → N = e * 15 → w = e * 6 → False) : m ≠ ordA 5 (2 ^ f) := by
  intro hm
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    exact h15 (l6_one h hm).1
  · obtain ⟨hN, hw', -⟩ := l6_top hf2 h hw hle hm
    exact htop f hf2 hN hw'

theorem ordA_eq_ordA_five {m g f : ℕ} (hm : 1 ≤ m) (hg : 1 ≤ g) (hf : 1 ≤ f)
    (he : ordA m (2 ^ g) = ordA 5 (2 ^ f)) : m = 5 ∧ g = f := by
  have hX := profile_idxA hm hg
  have hT := mul_succ_eq_two_mul_div_two m
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    obtain ⟨hN, h4⟩ := l6_one hX he
    have hm5 : m ≤ 5 := by
      by_contra hc
      have h1 : 6 * 7 ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
      have h2 : m * (m + 1) / 2 ≤ g * (m * (m + 1) / 2) := Nat.le_mul_of_pos_left _ hg
      omega
    interval_cases m
    · obtain rfl : g = 15 := by simpa using hN
      revert h4; simp only [idxA]; decide
    · obtain rfl : g = 5 := by norm_num at hN; omega
      revert h4; simp only [idxA]; decide
    · norm_num at hN; omega
    · norm_num at hN; omega
    · norm_num at hN; exact ⟨rfl, by omega⟩
  · obtain ⟨hN, hw, -⟩ := l6_top hf2 hX ⟨m + 1, by simp; omega, dvd_rfl⟩
      (fun k hk => idxA_le (by omega) hk) he
    generalize m * (m + 1) / 2 = T at hT hN
    have e1 : g * (m + 1) * m = g * (m + 1) * 5 := by
      calc g * (m + 1) * m = g * (m * (m + 1)) := by ring
        _ = 2 * (g * T) := by rw [hT]; ring
        _ = g * (m + 1) * 5 := by rw [hN, hw]; ring
    obtain rfl : m = 5 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
    exact ⟨rfl, by omega⟩

theorem ordTwistedA_ne_ordA_five {u g f : ℕ} (hu : 2 ≤ u) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedA u (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  fun h => ordA_ne_ordTwistedA (by norm_num) hf hu hg h.symm

theorem ordBC_ne_ordA_five {n g f : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordBC n (2 ^ g) ≠ ordA 5 (2 ^ f) := by
  intro he
  have hX := profile_idxBC (n := n) hg
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    obtain ⟨hN, -⟩ := l6_one hX he
    have hn3 : n ≤ 3 := by
      by_contra hc
      have h1 : 4 * 4 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
      have h2 : n * n ≤ g * (n * n) := Nat.le_mul_of_pos_left _ hg
      omega
    interval_cases n <;> omega
  · obtain ⟨hN, hw, hZ⟩ := l6_top hf2 hX ⟨n, by simp; omega, dvd_rfl⟩
      (fun k hk => idxBC_le (by omega) hk) he
    have h1 : g * n = f * 3 := by
      have : g * (2 * n) = 2 * (g * n) := by ring
      omega
    have e1 : g * n * n = g * n * 5 := by
      calc g * n * n = g * (n * n) := by ring
        _ = g * n * 5 := by rw [hN, h1]; ring
    obtain rfl : n = 5 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
    have hrel : 3 * f = 5 * g := by omega
    have hk : idxBC 5 g (g * (2 * 4)) := ⟨4, by simp, dvd_rfl⟩
    obtain ⟨i, hi, hd⟩ := (hZ _ (by omega) (by omega)).mp hk
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    have := dvd_of_rel (by omega) hrel hd
    interval_cases i <;> omega

theorem ordD_ne_ordA_five {n g f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordD n (2 ^ g) ≠ ordA 5 (2 ^ f) := by
  intro he
  have hX := profile_idxD (by omega : 1 ≤ n) hg
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    obtain ⟨hN, -⟩ := l6_one hX he
    rcases Nat.lt_or_ge n 5 with hn5 | hn5
    · obtain rfl : n = 4 := by omega
      norm_num at hN; omega
    · have h1 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hn5 (by omega)
      have h2 : n * (n - 1) ≤ g * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hg
      omega
  · obtain ⟨hN, hw, hZ⟩ := l6_top hf2 hX (Or.inr ⟨n - 1, by simp; omega, dvd_rfl⟩)
      (fun k hk => idxD_le (by omega) (by omega) hk) he
    have h1 : g * (n - 1) = f * 3 := by
      have : g * (2 * (n - 1)) = 2 * (g * (n - 1)) := by ring
      omega
    have e1 : g * (n - 1) * n = g * (n - 1) * 5 := by
      calc g * (n - 1) * n = g * (n * (n - 1)) := by ring
        _ = g * (n - 1) * 5 := by rw [hN, h1]; ring
    obtain rfl : n = 5 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
    have hrel : 3 * f = 4 * g := by omega
    have hk : idxD 5 g (g * (2 * 3)) := Or.inr ⟨3, by simp, dvd_rfl⟩
    obtain ⟨i, hi, hd⟩ := (hZ _ (by omega) (by omega)).mp hk
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    have := dvd_of_rel (by omega) hrel hd
    interval_cases i <;> omega

theorem ordTwistedD_six_eq {q : ℕ} (hq : Even q) :
    ordTwistedD 6 q = q ^ 30 * ((q ^ 6 + 1) * ((q ^ 2 - 1) *
      ((q ^ 4 - 1) * ((q ^ 6 - 1) * ((q ^ 8 - 1) * (q ^ 10 - 1)))))) := by
  have hodd : Odd (q ^ 6 + 1) := ((Nat.even_pow' (by norm_num)).mpr hq).add_one
  rw [ordTwistedD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd), Nat.div_one,
    show Finset.Icc 1 (6 - 1) = {1, 2, 3, 4, 5} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [Nat.reduceMul, Nat.reduceSub]
  ring

theorem ordA_five_mul_gcd (Q : ℕ) :
    ordA 5 Q * Nat.gcd 6 (Q - 1) =
      Q ^ 15 * ((Q ^ 2 - 1) * ((Q ^ 3 - 1) * ((Q ^ 4 - 1) * ((Q ^ 5 - 1) * (Q ^ 6 - 1))))) := by
  have hprod : ∏ i ∈ Finset.Icc 2 (5 + 1), (Q ^ i - 1) =
      (Q ^ 2 - 1) * ((Q ^ 3 - 1) * ((Q ^ 4 - 1) * ((Q ^ 5 - 1) * (Q ^ 6 - 1)))) := by
    rw [show Finset.Icc 2 (5 + 1) = {2, 3, 4, 5, 6} by decide, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
  have hdvd : Nat.gcd (5 + 1) (Q - 1) ∣
      Q ^ (5 * (5 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (5 + 1), (Q ^ i - 1) := by
    rw [hprod]
    exact (Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one Q 2).trans
      ((dvd_mul_right _ _).trans (dvd_mul_left _ _)))
  change ordA 5 Q * Nat.gcd (5 + 1) (Q - 1) = _
  rw [ordA, Nat.div_mul_cancel hdvd, hprod]

theorem ordTwistedD_six_ne_ordA_five {g : ℕ} (hg : 1 ≤ g) :
    ordTwistedD 6 (2 ^ g) ≠ ordA 5 (2 ^ (2 * g)) := by
  intro he
  have hq2 : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hqe : Even (2 ^ g) := (Nat.even_pow' (by omega)).mpr even_two
  have hQ : 2 ^ (2 * g) = (2 ^ g) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hQ] at he
  generalize 2 ^ g = q at hq2 hqe he
  have hD := ordTwistedD_six_eq hqe
  have hA := ordA_five_mul_gcd (q ^ 2)
  have hd6 : Nat.gcd 6 (q ^ 2 - 1) ≤ 6 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  generalize Nat.gcd 6 (q ^ 2 - 1) = d at hA hd6
  rw [← he, hD] at hA
  simp only [← pow_mul] at hA
  norm_num at hA
  have h4 : 16 ≤ q ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq2 4
  have h2 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq2 2
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h8 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h10 : 1 ≤ q ^ 10 := Nat.one_le_pow _ _ (by omega)
  have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
  have hC : 0 < q ^ 30 * ((q ^ 4 - 1) * ((q ^ 6 - 1) * ((q ^ 8 - 1) * (q ^ 10 - 1)))) := by
    have : 0 < q ^ 30 := by positivity
    have : 0 < q ^ 4 - 1 := by omega
    have : 0 < q ^ 6 - 1 := by
      have : q ^ 4 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    have : 0 < q ^ 8 - 1 := by
      have : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    have : 0 < q ^ 10 - 1 := by
      have : q ^ 4 ≤ q ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    positivity
  have key : q ^ 30 * ((q ^ 4 - 1) * ((q ^ 6 - 1) * ((q ^ 8 - 1) * (q ^ 10 - 1)))) *
      ((q ^ 6 + 1) * ((q ^ 2 - 1) * d)) =
      q ^ 30 * ((q ^ 4 - 1) * ((q ^ 6 - 1) * ((q ^ 8 - 1) * (q ^ 10 - 1)))) *
      ((q ^ 6 + 1) * (q ^ 6 - 1)) := by
    have e12 : q ^ 12 - 1 = (q ^ 6 + 1) * (q ^ 6 - 1) := by
      zify [h6, h12]; ring
    rw [← e12]
    linarith [hA]
  have k1 := Nat.eq_of_mul_eq_mul_left hC key
  have k2 := Nat.eq_of_mul_eq_mul_left (by omega) k1
  have e6 : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by
    zify [h6, (by omega : 1 ≤ q ^ 2)]; ring
  rw [e6] at k2
  have k3 := Nat.eq_of_mul_eq_mul_left (by omega) k2
  omega

theorem ordTwistedD_ne_ordA_five {n g f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedD n (2 ^ g) ≠ ordA 5 (2 ^ f) := by
  intro he
  have hX := profile_idx2D (by omega : 1 ≤ n) hg
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    obtain ⟨hN, -⟩ := l6_one hX he
    rcases Nat.lt_or_ge n 5 with hn5 | hn5
    · obtain rfl : n = 4 := by omega
      norm_num at hN; omega
    · have h1 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hn5 (by omega)
      have h2 : n * (n - 1) ≤ g * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hg
      omega
  · have hgn : 0 < g * n := Nat.mul_pos (by omega) (by omega)
    obtain ⟨hN, hw, -⟩ := l6_top hf2 hX
      (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd hgn h; omega⟩)
      (fun k hk => idx2D_le (by omega) (by omega) hk) he
    have h1 : g * n = f * 3 := by omega
    have e1 : g * n * (n - 1) = g * n * 5 := by
      calc g * n * (n - 1) = g * (n * (n - 1)) := by ring
        _ = g * n * 5 := by rw [hN, h1]; ring
    have hn6 : n - 1 = 5 := Nat.eq_of_mul_eq_mul_left hgn e1
    obtain rfl : n = 6 := by omega
    obtain rfl : f = 2 * g := by omega
    exact ordTwistedD_six_ne_ordA_five hg he

end CFSG.SeitzReduction.F4Pilot
