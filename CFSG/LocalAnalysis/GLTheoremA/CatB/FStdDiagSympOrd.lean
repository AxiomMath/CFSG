module

public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem fstdSymp_small_exp {m N : ℕ} (hm : m = 360 ∨ m = 25920) (h : ∃ r, Odd r ∧ m = 2 ^ N * r) :
    N = 3 ∨ N = 6 := by
  obtain ⟨r, hr, hmr⟩ := h
  rcases hm with rfl | rfl
  · exact Or.inl (eq_of_two_pow_mul_odd hr (by decide : Odd 45) (hmr.symm.trans (by norm_num)))
  · exact Or.inr (eq_of_two_pow_mul_odd hr (by decide : Odd 405) (hmr.symm.trans (by norm_num)))

theorem fstdSymp_ordA_ne {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (h2 : (n, 2 ^ f) ≠ (2, 2))
    (h3 : (n, 2 ^ f) ≠ (2, 3)) :
    ¬ (ordA (n - 1) (2 ^ f) = 360 ∨ ordA (n - 1) (2 ^ f) = 25920) := by
  intro hm
  obtain ⟨r, hr, hr'⟩ := (profile_ordA (n := n - 1) (f := f) (by omega) hf).two
  have hN := fstdSymp_small_exp hm ⟨r, hr, hr'⟩
  have hn4 : n ≤ 4 := by
    by_contra hcon
    have h20 : 4 * 5 ≤ (n - 1) * (n - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h10 : 10 ≤ (n - 1) * (n - 1 + 1) / 2 := by omega
    have : 10 ≤ f * ((n - 1) * (n - 1 + 1) / 2) := le_trans h10 (Nat.le_mul_of_pos_left _ hf)
    omega
  interval_cases n
  · have hf' : f = 3 ∨ f = 6 := by omega
    rcases hf' with rfl | rfl <;> revert hm <;> decide +kernel
  · have hf' : f = 1 ∨ f = 2 := by omega
    rcases hf' with rfl | rfl <;> revert hm <;> decide +kernel
  · have hf' : f = 1 := by omega
    subst hf'
    revert hm
    decide +kernel

theorem fstdSymp_ordTwistedA_cases {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) (h : (n, 2 ^ f) ≠ (3, 2))
    (hm : ordTwistedA (n - 1) (2 ^ f) = 360 ∨ ordTwistedA (n - 1) (2 ^ f) = 25920) :
    n = 4 ∧ f = 1 := by
  obtain ⟨r, hr, hr'⟩ := (profile_ordTwistedA (n := n - 1) (g := f) (by omega) hf).two
  have hN := fstdSymp_small_exp hm ⟨r, hr, hr'⟩
  have hn4 : n ≤ 4 := by
    by_contra hcon
    have h20 : 4 * 5 ≤ (n - 1) * (n - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h10 : 10 ≤ (n - 1) * (n - 1 + 1) / 2 := by omega
    have : 10 ≤ f * ((n - 1) * (n - 1 + 1) / 2) := le_trans h10 (Nat.le_mul_of_pos_left _ hf)
    omega
  interval_cases n
  · have hf' : f = 1 ∨ f = 2 := by omega
    rcases hf' with rfl | rfl
    · exact absurd rfl h
    · exact absurd hm (by decide +kernel)
  · have hf' : f = 1 := by omega
    exact ⟨rfl, hf'⟩

theorem fstdSymp_ordBC_ne {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) :
    ¬ (ordBC n (2 ^ f) = 360 ∨ ordBC n (2 ^ f) = 25920) := by
  intro hm
  obtain ⟨r, hr, hr'⟩ := (profile_ordBC (n := n) (f := f) hf).two
  have hN := fstdSymp_small_exp hm ⟨r, hr, hr'⟩
  have h4 : 4 ≤ n * n := Nat.mul_le_mul hn hn
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    omega
  · have h9 : 9 ≤ n * n := Nat.mul_le_mul h3 h3
    have : 9 ≤ f * (n * n) := le_trans h9 (Nat.le_mul_of_pos_left _ hf)
    omega

theorem fstdSymp_ordD_ne {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) :
    ¬ (ordD n (2 ^ f) = 360 ∨ ordD n (2 ^ f) = 25920) := by
  intro hm
  obtain ⟨r, hr, hr'⟩ := (profile_ordD (n := n) (f := f) (by omega) hf).two
  have hN := fstdSymp_small_exp hm ⟨r, hr, hr'⟩
  have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  have : 12 ≤ f * (n * (n - 1)) := le_trans h12 (Nat.le_mul_of_pos_left _ hf)
  omega

theorem fstdSymp_ordTwistedD_ne {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) :
    ¬ (ordTwistedD n (2 ^ f) = 360 ∨ ordTwistedD n (2 ^ f) = 25920) := by
  intro hm
  obtain ⟨r, hr, hr'⟩ := (profile_ordTwistedD (n := n) (f := f) (by omega) hf).two
  have hN := fstdSymp_small_exp hm ⟨r, hr, hr'⟩
  have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  have : 12 ≤ f * (n * (n - 1)) := le_trans h12 (Nat.le_mul_of_pos_left _ hf)
  omega

theorem fstdSymp_classical_order {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (h : StatedClassicalModel G t n 2 f)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hord : Nat.card G = 360 ∨ Nat.card G = 25920) :
    t = .PSU ∧ n = 4 ∧ f = 1 ∧ Nat.card G = 25920 := by
  have hcard := card_statedClassicalModel_two h
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨⟨-, hf, hn, h2, h3⟩, -⟩ := h
    rw [hcard.1 rfl] at hord
    exact absurd hord (fstdSymp_ordA_ne hn hf h2 h3)
  · obtain ⟨⟨-, hf, hn, hne⟩, -⟩ := h
    rw [hcard.2.1 rfl] at hord
    obtain ⟨rfl, rfl⟩ := fstdSymp_ordTwistedA_cases hn hf hne hord
    exact ⟨rfl, rfl, rfl, by rw [hcard.2.1 rfl]; decide +kernel⟩
  · obtain ⟨⟨-, hf, hn, -⟩, -⟩ := h
    rw [hcard.2.2.1 rfl] at hord
    exact absurd hord (fstdSymp_ordBC_ne hn hf)
  · obtain ⟨⟨-, hf, hn⟩, -⟩ := h
    rw [hcard.2.2.2.1 rfl] at hord
    exact absurd hord (fstdSymp_ordD_ne hn hf)
  · obtain ⟨⟨-, hf, hn⟩, -⟩ := h
    rw [hcard.2.2.2.2 rfl] at hord
    exact absurd hord (fstdSymp_ordTwistedD_ne hn hf)

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
