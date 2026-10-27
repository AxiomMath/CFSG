module

public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverCommutator

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Semidihedral CFSG.Open

variable {P : Type*} [Group P]

theorem orderOf_semidihedral_r_pow (q : ℕ) :
    orderOf (r (q + 4) ^ (2 ^ (q + 2) - 2)) = 2 ^ (q + 2) := by
  obtain ⟨C, hC, hCodd⟩ : ∃ C, 2 ^ (q + 1) = C + 1 ∧ Odd C := by
    refine ⟨2 ^ (q + 1) - 1, by have := Nat.one_le_two_pow (n := q + 1); omega, ?_⟩
    have h := Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero q⟩
    have := Nat.one_le_two_pow (n := q + 1)
    rcases h with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  have h2 : 2 ^ (q + 2) = 2 * (C + 1) := by rw [pow_succ, hC]; ring
  have hord : orderOf (r (q + 4)) = 4 * (C + 1) := by
    rw [orderOf_r (q + 4) (by omega), modulus, show q + 4 - 1 = q + 1 + 2 by omega, pow_add, hC]
    ring
  have hsub : 2 ^ (q + 2) - 2 = 2 * C := by omega
  rw [hsub, show 2 ^ (q + 2) = 2 ^ (q + 1 + 1) by rfl]
  apply orderOf_eq_prime_pow
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord, hC]
    rintro ⟨d, hd⟩
    have h' : (2 * C) * (C + 1) = (4 * d) * (C + 1) := by rw [hd]; ring
    have h'' := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos C) h'
    obtain ⟨k, hk⟩ := hCodd
    omega
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord, pow_succ, hC]
    exact ⟨C, by ring⟩

theorem eq_one_of_semidihedral {n : ℕ} (hn : 4 ≤ n) (ψ : P →* SemidihedralGroup n)
    (hψ : Function.Surjective ψ) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g) {z : P}
    (hz : ψ z = 1) (hzc : z ∈ commutator P) : z = 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 4 := ⟨n - 4, by omega⟩
  obtain ⟨r₀, hr₀⟩ := hψ (r (q + 4))
  obtain ⟨s₀, hs₀⟩ := hψ (s (q + 4))
  set N := 2 ^ (q + 2) with hN
  have hN4 : 4 ≤ N := by
    rw [hN, pow_add]
    have := Nat.one_le_two_pow (n := q)
    omega
  have hsr : s (q + 4) * r (q + 4) * (s (q + 4))⁻¹ = r (q + 4) ^ (N - 1) := by
    rw [s_conj_r, show q + 4 - 2 = q + 2 by omega]
  have hsnot : s (q + 4) ∉ Subgroup.zpowers (r (q + 4)) := by
    rw [← parityHom_ker (q + 4) (by omega), MonoidHom.mem_ker]
    simp [parityHom, modelS]
  set σr := s₀ * r₀ * s₀⁻¹ with hσr_def
  set w := r₀⁻¹ * σr with hw_def
  have hcomm : commutator P ≤ Subgroup.zpowers w :=
    commutator_le_zpowers_of_index_two ψ hψ hcen
      (by rw [hr₀]; exact rotation_index (q + 4) (by omega)) (by rw [hs₀, hr₀]; exact hsnot)
  have hψσ : ψ σr = r (q + 4) ^ (N - 1) := by
    rw [hσr_def, map_mul, map_mul, map_inv, hr₀, hs₀, hsr]
  have hψw : ψ w = r (q + 4) ^ (N - 2) := by
    rw [hw_def, map_mul, map_inv, hψσ, hr₀, show N - 1 = (N - 2) + 1 by omega, pow_succ',
      inv_mul_cancel_left]
  have hs2 : ψ (s₀ * s₀) = 1 := by
    rw [map_mul, hs₀, ← pow_two, s_sq]
  have hσσ : s₀ * σr * s₀⁻¹ = r₀ := by
    calc s₀ * σr * s₀⁻¹ = (s₀ * s₀) * r₀ * (s₀ * s₀)⁻¹ := by rw [hσr_def]; group
      _ = r₀ := by rw [← hcen _ hs2 r₀, mul_inv_cancel_right]
  have hc₁ : ψ ((r₀ ^ (N - 1))⁻¹ * σr) = 1 := by
    rw [map_mul, map_inv, map_pow, hr₀, hψσ, inv_mul_cancel]
  set c₁ := (r₀ ^ (N - 1))⁻¹ * σr with hc₁_def
  have hσr : σr = r₀ ^ (N - 1) * c₁ := by rw [hc₁_def, mul_inv_cancel_left]
  have hw : w = r₀ ^ (N - 2) * c₁ := by
    rw [hw_def, hσr, ← mul_assoc, show N - 1 = (N - 2) + 1 by omega, pow_succ',
      inv_mul_cancel_left]
  have hcr : ∀ a : ℕ, Commute (r₀ ^ a) c₁ := fun a => hcen c₁ hc₁ (r₀ ^ a)
  have hσw₁ : s₀ * w * s₀⁻¹ = w⁻¹ := by
    calc s₀ * w * s₀⁻¹ = σr⁻¹ * (s₀ * σr * s₀⁻¹) := by rw [hw_def, hσr_def]; group
      _ = σr⁻¹ * r₀ := by rw [hσσ]
      _ = w⁻¹ := by rw [hw_def]; group
  have hσw₂ : s₀ * w * s₀⁻¹ = w ^ (N - 1) := by
    have hsc : s₀ * c₁ * s₀⁻¹ = c₁ := by rw [hcen c₁ hc₁ s₀, mul_inv_cancel_right]
    calc s₀ * w * s₀⁻¹ = (s₀ * r₀ ^ (N - 2) * s₀⁻¹) * (s₀ * c₁ * s₀⁻¹) := by rw [hw]; group
      _ = (r₀ ^ (N - 1) * c₁) ^ (N - 2) * c₁ := by rw [← conj_pow, hsc, ← hσr_def, hσr]
      _ = r₀ ^ ((N - 1) * (N - 2)) * c₁ ^ (N - 2 + 1) := by
          rw [(hcr _).mul_pow, ← pow_mul, pow_succ, mul_assoc]
      _ = w ^ (N - 1) := by
          rw [hw, (hcr _).mul_pow, ← pow_mul, mul_comm (N - 2), show N - 2 + 1 = N - 1 by omega]
  have hwN : w ^ N = 1 := by
    rw [show N = (N - 1) + 1 by omega, pow_succ, ← hσw₂, hσw₁, inv_mul_cancel]
  have hordw : orderOf w = N := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hwN)
    have := orderOf_map_dvd ψ w
    rwa [hψw, hN, orderOf_semidihedral_r_pow q] at this
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hcomm hzc)
  rw [map_zpow, hψw, ← orderOf_dvd_iff_zpow_eq_one, orderOf_semidihedral_r_pow q, ← hN,
    ← hordw, orderOf_dvd_iff_zpow_eq_one] at hz
  exact hz

end CFSG.ProperTwoGeneratedCore.Lemma37
