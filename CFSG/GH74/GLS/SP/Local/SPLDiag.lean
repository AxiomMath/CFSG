module

public import CFSG.GH74.GLS.SP.Local.SPLDiagB
public import CFSG.GH74.GLS.SP.Local.SPLDiagC

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem diagonalImpossible : DiagonalImpossible := by
  intro X _ _ z t A T₁ L ctx hL hLz hAB hAD
  have hz2 := ctx.z_sq
  have hMcard := diag_card_M ctx hL hAB hAD
  have hzN := diag_z_mem_normalizer (L := L) hz2
  have hM1 := diag_card_sup_zpowers hz2 hzN (diag_z_not_mem ctx hAB hLz)
  obtain ⟨k, hk⟩ := ctx.T₁_pgrp.exists_card_eq
  have hTA : Nat.card ↥T₁ ∣ Nat.card ↥A := Subgroup.card_dvd_of_le ctx.T₁_le
  rw [hk] at hTA
  have hQ : ∀ (Q : Subgroup X) (n : ℕ), 2 ^ n ∣ Nat.card ↥Q → 2 ^ n ≤ 2 * (2 ^ k) ^ 2 :=
    fun Q n hn => by
      have := diag_pow_dvd_le ctx Q hn
      rwa [hk] at this
  have hAne : Nat.card ↥A ≠ 0 := Nat.card_pos.ne'
  have hodd : Odd (Nat.card ↥(L ⊓ conjSub z⁻¹ L)) := by
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    have h2c : 2 ^ 1 ∣ Nat.card ↥(L ⊓ conjSub z⁻¹ L) := by
      simpa using even_iff_two_dvd.1 hnot
    have hdvd : 2 ^ 1 * Nat.card ↥(L ⊔ conjSub z⁻¹ L) ∣
        Nat.card ↥((L ⊔ conjSub z⁻¹ L ⊔ zpowers z) ⊔ zpowers t) := by
      rw [pow_one, ← hM1]
      exact Subgroup.card_dvd_of_le le_sup_left
    have := diag_arith (e := 1) hAne hMcard hTA (hQ _) hdvd h2c
    omega
  have htM : t ∈ L ⊔ conjSub z⁻¹ L := by
    by_contra htM
    have ht1 : t ∉ L ⊔ conjSub z⁻¹ L ⊔ zpowers z := by
      intro h
      rcases diag_mem_sup_zpowers hz2 hzN h with h | h
      · exact htM h
      · apply diag_zt_not_mem ctx hAB hLz
        rwa [← ctx.t_central z] at h
    have hQcard := diag_card_sup_zpowers ctx.t_sq
      (diag_mem_normalizer_of_central ctx.t_central _) ht1
    have hdvd : 2 ^ 2 * Nat.card ↥(L ⊔ conjSub z⁻¹ L) ∣
        Nat.card ↥((L ⊔ conjSub z⁻¹ L ⊔ zpowers z) ⊔ zpowers t) := by
      rw [hQcard, hM1]
      exact ⟨1, by ring⟩
    have := diag_arith (e := 2) (b := 0) hAne hMcard hTA (hQ _) hdvd (by simp)
    omega
  exact diag_t_not_mem ctx hL hAB hAD hodd htM

end CFSG.GH74.GLS.SP.Local
