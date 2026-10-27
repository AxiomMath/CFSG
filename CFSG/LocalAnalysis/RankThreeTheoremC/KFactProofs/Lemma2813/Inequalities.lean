module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Generation
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.FixPoints

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

theorem ineq_three_pts :
    ∃ p q r : V3, p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ r ≠ p + q := by
  refine ⟨![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

section CT

variable {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]

theorem ineq_triple_inf (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) :
    ∃ p q r : V3, p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧
      fixSub M (Spt p) ⊓ fixSub M (Spt q) ⊓ fixSub M (Spt r) = ⊥ := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, hrpq⟩ := ineq_three_pts
  refine ⟨p, q, r, hp, hq, hr, ?_⟩
  rw [← fixSub_sup, ← fixSub_sup, Spt_sup_three hp hq hr hpq hpr hqr hrpq]
  refine le_antisymm ?_ bot_le
  intro m hm
  rw [AddSubgroup.mem_bot]
  exact hM0 m (fun g => hm g (Subgroup.mem_top g))

theorem card_fixSub_Spt_sq {p q : V3} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    Nat.card (fixSub M (Spt p)) * Nat.card (fixSub M (Spt p)) ≤
      Nat.card M * Nat.card (fixSub M (Spt p ⊔ Spt q)) := by
  have h1 := card_inf_ge (fixSub M (Spt p)) (fixSub M (Spt q))
  rw [← fixSub_sup, card_fixSub_Spt hq hp] at h1
  exact h1

theorem card_fixSub_Spt_cube (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) {p₀ : V3}
    (hp₀ : p₀ ≠ 0) : Nat.card (fixSub M (Spt p₀)) ^ 3 ≤ Nat.card M ^ 2 := by
  obtain ⟨p, q, r, hp, hq, hr, hbot⟩ := ineq_triple_inf (M := M) hM0
  have h1 := card_inf_ge (fixSub M (Spt p)) (fixSub M (Spt q))
  have h2 := card_inf_ge (fixSub M (Spt p) ⊓ fixSub M (Spt q)) (fixSub M (Spt r))
  rw [hbot, AddSubgroup.card_bot] at h2
  rw [card_fixSub_Spt hp hp₀, card_fixSub_Spt hq hp₀] at h1
  rw [card_fixSub_Spt hr hp₀] at h2
  generalize Nat.card (fixSub M (Spt p₀)) = a at h1 h2 ⊢
  generalize Nat.card M = n at h1 h2 ⊢
  generalize Nat.card (fixSub M (Spt p) ⊓ fixSub M (Spt q) : AddSubgroup M) = c at h1 h2
  calc a ^ 3 = a * (a * a) := by ring
    _ ≤ a * (n * c) := Nat.mul_le_mul_left _ h1
    _ = n * (c * a) := by ring
    _ ≤ n * (n * 1) := Nat.mul_le_mul_left _ h2
    _ = n ^ 2 := by ring

theorem card_fixSub_Spt_lt (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) (hne : ∃ m : M, m ≠ 0)
    {p₀ : V3} (hp₀ : p₀ ≠ 0) : Nat.card (fixSub M (Spt p₀)) < Nat.card M := by
  have key : ∀ x : V3, x ≠ 0 → fixSub M (Spt p₀) = ⊤ → fixSub M (Spt x) = ⊤ := by
    intro x hx h
    rw [← AddSubgroup.card_eq_iff_eq_top] at h ⊢
    rw [card_fixSub_Spt hx hp₀]
    exact h
  have hlt : fixSub M (Spt p₀) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨p, q, r, hp, hq, hr, hbot⟩ := ineq_triple_inf (M := M) hM0
    rw [key p hp htop, key q hq htop, key r hr htop] at hbot
    obtain ⟨m, hm⟩ := hne
    apply hm
    have hmem : m ∈ (⊥ : AddSubgroup M) := by
      rw [← hbot]
      simp
    simpa using hmem
  have := AddSubgroup.card_lt_of_lt hlt
  rwa [AddSubgroup.card_top] at this

end CT

theorem ct_arith (n a b : ℕ) (hn : ∃ k, n = 2 ^ k) (ha : ∃ k, a = 2 ^ k) (hb : ∃ k, b = 2 ^ k)
    (ha2 : 2 ≤ a) (han : a < n) (hoff : n ≤ 4 * a) (h3 : a ^ 3 ≤ n ^ 2)
    (h1 : 7 * a + 8 ≤ n + 14 * b) (h2 : 3 * b ≤ a + 2) (h4 : a * a ≤ n * b) :
    (n = 8 ∧ a = 2 ∧ b = 1) ∨ (n = 8 ∧ a = 4 ∧ b = 2) ∨ (n = 16 ∧ a = 4 ∧ b = 2) ∨
      (n = 64 ∧ a = 16 ∧ b = 4) := by
  have hsq : n ^ 2 ≤ (4 * a) ^ 2 := Nat.pow_le_pow_left hoff 2
  have ha16 : a ≤ 16 := by
    have h5 : a * (a * a) ≤ 16 * (a * a) := by nlinarith
    exact Nat.le_of_mul_le_mul_right h5 (by positivity)
  have hn64 : n ≤ 64 := by omega
  have hb6 : b ≤ 6 := by omega
  obtain ⟨k, rfl⟩ := hn
  obtain ⟨j, rfl⟩ := ha
  obtain ⟨l, rfl⟩ := hb
  have hk : k < 7 := by
    by_contra hk
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 hk)
    norm_num at this
    omega
  have hj : j < 5 := by
    by_contra hj
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 hj)
    norm_num at this
    omega
  have hl : l < 3 := by
    by_contra hl
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 hl)
    norm_num at this
    omega
  clear hsq ha16 hn64 hb6
  interval_cases k <;> interval_cases j <;> interval_cases l <;> omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
