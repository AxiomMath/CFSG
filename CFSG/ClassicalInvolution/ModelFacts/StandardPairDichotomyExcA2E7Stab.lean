module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {k : Type} [Field k]

theorem rootCharStabilizer_pairDiag_le_partnerE7 (hk : (-1 : kˣ) ≠ 1)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsPartnerE7 δ) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → c ^ j ≠ 1) {w : WeylGroup .E7}
    (hw : w ∈ rootCharStabilizer (pairDiagE7 δ c)) :
    w ∈ kernelReflectionGroup (pairDiagE7 δ c) := by
  obtain ⟨hδ, hδθ⟩ := hδ
  classical
  have hbasis : ∀ j : Fin (Tag.rank .E7),
      iform thetaE7 (w • Pi.single j 1) = iform thetaE7 (Pi.single j 1) ∧
        Even (iform δ (w • Pi.single j 1) - iform δ (Pi.single j 1)) := by
    intro j
    have hroot : IsRoot .E7 (w • (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ)) :=
      IsRoot.smul (isRoot_single _ j) w
    have h := hw (Pi.single j 1)
    rw [rootChar_pairDiagE7, rootChar_pairDiagE7] at h
    have b1 := abs_iform_thetaE7_le _ (mem_rootFinset.2 hroot)
    have b2 : iform thetaE7 (Pi.single j 1) = 0 ∨ iform thetaE7 (Pi.single j 1) = 1 := by
      rw [iform_thetaE7_single]
      split_ifs <;> simp
    rw [abs_le] at b1
    set x := iform δ (w • Pi.single j 1)
    set x' := iform δ (Pi.single j 1)
    set y := iform thetaE7 (w • Pi.single j 1)
    set y' := iform thetaE7 (Pi.single j 1)
    have hpow : ∀ n : ℤ, (c ^ n) ^ 2 = c ^ (2 * n) := fun n => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
      norm_cast
    have h2 : ((-1 : kˣ) ^ x * c ^ y) ^ 2 = ((-1 : kˣ) ^ x' * c ^ y') ^ 2 := by rw [h]
    rw [mul_pow, mul_pow, neg_one_zpow_sq, neg_one_zpow_sq, one_mul, one_mul, hpow, hpow] at h2
    have h3 : c ^ (2 * (y - y')) = 1 := by
      rw [mul_sub, zpow_sub, h2, mul_inv_cancel]
    have hyy : y = y' := by
      have := eq_zero_of_zpow_eq_one hc (m := 2 * (y - y')) (N := 8) (by
        rw [abs_le]; omega) h3
      omega
    refine ⟨hyy, ?_⟩
    rw [hyy] at h
    have h4 : (-1 : kˣ) ^ x = (-1 : kˣ) ^ x' := mul_right_cancel h
    have h5 : (-1 : kˣ) ^ (x - x') = 1 := by rw [zpow_sub, h4, mul_inv_cancel]
    by_contra he
    have h6 : (-1 : kˣ) ^ (x - x') = -1 := by rw [neg_one_zpow_eq_ite]; simp [he]
    exact hk (h6.symm.trans h5)
  have hwθ : w • thetaE7 = thetaE7 := by
    set X := w⁻¹ • thetaE7 - thetaE7 with hX
    have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
      intro j
      have h1 := (hbasis j).1
      have h2 : iform thetaE7 (w • Pi.single j 1) = iform (w⁻¹ • thetaE7) (Pi.single j 1) := by
        rw [← iform_smul_smul w⁻¹ thetaE7 (w • Pi.single j 1), inv_smul_smul]
      rw [hX, iform_sub_left, ← h2, h1, sub_self]
    have hX0 : X = 0 := by
      by_contra hne
      have hpos := iform_self_pos hne
      rw [iform_eq_sum_single X X] at hpos
      simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
      exact lt_irrefl _ hpos
    have : w⁻¹ • thetaE7 = thetaE7 := sub_eq_zero.1 hX0
    calc w • thetaE7 = w • (w⁻¹ • thetaE7) := by rw [this]
      _ = thetaE7 := smul_inv_smul w _
  have hρ : w⁻¹ • δ = δ ∨ w⁻¹ • δ = -δ := by
    refine twinFree_E7 (IsRoot.smul hδ w⁻¹) hδ fun j => ?_
    have h2 : iform δ (w • Pi.single j 1) = iform (w⁻¹ • δ) (Pi.single j 1) := by
      rw [← iform_smul_smul w⁻¹ δ (w • Pi.single j 1), inv_smul_smul]
    rw [iform_sub_left, ← h2]
    exact (hbasis j).2
  have hwδ : w • δ = δ ∨ w • δ = -δ := by
    rcases hρ with h | h
    · left
      calc w • δ = w • (w⁻¹ • δ) := by rw [h]
        _ = δ := smul_inv_smul w _
    · right
      have : w • (w⁻¹ • δ) = w • (-δ) := by rw [h]
      rw [smul_inv_smul, smul_neg] at this
      exact (neg_eq_iff_eq_neg.1 this.symm).symm ▸ rfl
  have hwδ : w • δ = δ := by
    rcases hwδ with h | h
    · exact h
    · exfalso
      have h1 : iform thetaE7 (w • δ) = iform thetaE7 δ := by
        conv_lhs => rw [← hwθ]
        exact iform_smul_smul w thetaE7 δ
      rw [h, show (-δ : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_right] at h1
      omega
  exact mem_kernelReflectionGroup_of_fixes_E7 hwδ hwθ

end CFSG.ClassicalInvolution.ModelFacts.Levi
