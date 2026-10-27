module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {k : Type} [Field k]

theorem rootCharStabilizer_pairDiagF4_le_partner (hk : (-1 : kˣ) ≠ 1)
    {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsPartnerF4 δ) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → c ^ j ≠ 1) {w : WeylGroup .F4}
    (hw : w ∈ rootCharStabilizer (pairDiagF4 δ c)) :
    w ∈ kernelReflectionGroup (pairDiagF4 δ c) := by
  classical
  obtain ⟨hδr, hl, hδθ⟩ := hδ
  have hθev := even_iform_of_long_F4 isRoot_thetaF4 iform_thetaF4_self
  have hδev := even_iform_of_long_F4 hδr hl
  have hbasis : ∀ j : Fin (Tag.rank .F4),
      iform thetaF4 (w • Pi.single j 1) = iform thetaF4 (Pi.single j 1) ∧
        (4 : ℤ) ∣ iform δ (w • Pi.single j 1) - iform δ (Pi.single j 1) := by
    intro j
    have hroot : IsRoot .F4 (w • (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ)) :=
      IsRoot.smul (isRoot_single _ j) w
    have h := hw (Pi.single j 1)
    rw [rootChar_pairDiagF4 hδr hl, rootChar_pairDiagF4 hδr hl] at h
    have b1 := abs_iform_thetaF4_le _ (mem_rootFinset.2 hroot)
    have b2 : |iform thetaF4 (Pi.single j 1)| ≤ 2 := by
      rw [iform_thetaF4_single]
      split_ifs <;> simp
    rw [abs_le] at b1 b2
    obtain ⟨a, ha⟩ := hδev (w • Pi.single j 1)
    obtain ⟨a', ha'⟩ := hδev (Pi.single j 1)
    obtain ⟨b, hb⟩ := hθev (w • Pi.single j 1)
    obtain ⟨b', hb'⟩ := hθev (Pi.single j 1)
    have e1 : iform δ (w • Pi.single j 1) / 2 = a := by omega
    have e2 : iform δ (Pi.single j 1) / 2 = a' := by omega
    have e3 : iform thetaF4 (w • Pi.single j 1) / 2 = b := by omega
    have e4 : iform thetaF4 (Pi.single j 1) / 2 = b' := by omega
    rw [e1, e2, e3, e4] at h
    have hpow : ∀ n : ℤ, (c ^ n) ^ 2 = c ^ (2 * n) := fun n => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
      norm_cast
    have h2 : ((-1 : kˣ) ^ a * c ^ b) ^ 2 = ((-1 : kˣ) ^ a' * c ^ b') ^ 2 := by rw [h]
    rw [mul_pow, mul_pow, neg_one_zpow_sq, neg_one_zpow_sq, one_mul, one_mul, hpow, hpow] at h2
    have h3 : c ^ (2 * (b - b')) = 1 := by
      rw [mul_sub, zpow_sub, h2, mul_inv_cancel]
    have hbb : b = b' := by
      have := eq_zero_of_zpow_eq_one hc (m := 2 * (b - b')) (N := 8) (by
        rw [abs_le]; omega) h3
      omega
    refine ⟨by rw [hb, hb', hbb], ?_⟩
    rw [hbb] at h
    have h4 : (-1 : kˣ) ^ a = (-1 : kˣ) ^ a' := mul_right_cancel h
    have h5 : (-1 : kˣ) ^ (a - a') = 1 := by rw [zpow_sub, h4, mul_inv_cancel]
    have h6 : Even (a - a') := by
      by_contra he
      have h7 : (-1 : kˣ) ^ (a - a') = -1 := by rw [neg_one_zpow_eq_ite]; simp [he]
      exact hk (h7.symm.trans h5)
    obtain ⟨t, ht⟩ := h6
    exact ⟨t, by omega⟩
  have hwθ : w • thetaF4 = thetaF4 := by
    set X := w⁻¹ • thetaF4 - thetaF4 with hX
    have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
      intro j
      have h1 := (hbasis j).1
      have h2 : iform thetaF4 (w • Pi.single j 1) = iform (w⁻¹ • thetaF4) (Pi.single j 1) := by
        rw [← iform_smul_smul w⁻¹ thetaF4 (w • Pi.single j 1), inv_smul_smul]
      rw [hX, iform_sub_left, ← h2, h1, sub_self]
    have hX0 : X = 0 := by
      by_contra hne
      have hpos := iform_self_pos hne
      rw [iform_eq_sum_single X X] at hpos
      simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
      exact lt_irrefl _ hpos
    have : w⁻¹ • thetaF4 = thetaF4 := sub_eq_zero.1 hX0
    calc w • thetaF4 = w • (w⁻¹ • thetaF4) := by rw [this]
      _ = thetaF4 := smul_inv_smul w _
  have hρ : w⁻¹ • δ = δ ∨ w⁻¹ • δ = -δ := by
    set ρ := w⁻¹ • δ with hρdef
    have hρroot : IsRoot .F4 ρ := IsRoot.smul hδr w⁻¹
    have hρρ : iform ρ ρ = 4 := by
      rw [hρdef, iform_smul_smul, hl]
    have hdiv : ∀ j, (4 : ℤ) ∣ iform (ρ - δ) (Pi.single j 1) := by
      intro j
      have h2 : iform δ (w • Pi.single j 1) = iform ρ (Pi.single j 1) := by
        rw [← iform_smul_smul w⁻¹ δ (w • Pi.single j 1), inv_smul_smul]
      rw [iform_sub_left, ← h2]
      exact (hbasis j).2
    obtain ⟨Y, hY, hY4⟩ := exists_eq_two_smul_F4 _ hdiv
    have ht := abs_iform_le_four_F4 hρroot hδr
    rw [abs_le] at ht
    have hnorm : iform (ρ - δ) (ρ - δ) = 8 - 2 * iform ρ δ := by
      rw [iform_sub_left, iform_sub_right, iform_sub_right, hρρ, hl, iform_comm δ ρ]
      ring
    have hnorm2 : iform (ρ - δ) (ρ - δ) = 4 * iform Y Y := by
      rw [hY, iform_smul_left, iform_smul_right]
      ring
    obtain ⟨m, hm⟩ := hY4
    have hcases : iform ρ δ = 4 ∨ iform ρ δ = -4 := by omega
    rcases hcases with h2 | h2
    · left
      by_contra hne
      have := iform_self_pos (sub_ne_zero.2 hne)
      omega
    · right
      by_contra hne
      have hne' : ρ + δ ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
      have := iform_self_pos hne'
      rw [iform_add_left, iform_add_right, iform_add_right, hρρ, hl, iform_comm δ ρ] at this
      omega
  have hwδ : w • δ = δ := by
    have hwδ' : w • δ = δ ∨ w • δ = -δ := by
      rcases hρ with h | h
      · left
        calc w • δ = w • (w⁻¹ • δ) := by rw [h]
          _ = δ := smul_inv_smul w _
      · right
        have : w • (w⁻¹ • δ) = w • (-δ) := by rw [h]
        rw [smul_inv_smul, smul_neg] at this
        exact (neg_eq_iff_eq_neg.1 this.symm).symm ▸ rfl
    rcases hwδ' with h | h
    · exact h
    · exfalso
      have h1 : iform thetaF4 (w • δ) = iform thetaF4 δ := by
        conv_lhs => rw [← hwθ]
        exact iform_smul_smul w thetaF4 δ
      rw [h, show (-δ : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_right] at h1
      omega
  exact mem_kernelReflectionGroup_of_fixes_F4 hδr hl hwδ hwθ

end CFSG.ClassicalInvolution.ModelFacts.Levi
