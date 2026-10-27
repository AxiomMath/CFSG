module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Data
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Stab

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {k : Type} [Field k]

@[expose] noncomputable def pairDiagE6 (δ : Fin (Tag.rank .E6) → ℤ) (c : kˣ) :
    Fin (Tag.rank .E6) → kˣ :=
  thetaDiag δ (-1) * thetaDiag thetaE6 c

theorem rootChar_pairDiagE6 (δ : Fin (Tag.rank .E6) → ℤ) (c : kˣ) (v : Fin (Tag.rank .E6) → ℤ) :
    rootChar (pairDiagE6 δ c) v = (-1 : kˣ) ^ iform δ v * c ^ iform thetaE6 v := by
  rw [pairDiagE6, rootChar_mul, rootChar_thetaDiag, rootChar_thetaDiag]

theorem mem_kernelReflectionGroup_of_fixes_E6 {δ : Fin (Tag.rank .E6) → ℤ} {c : kˣ}
    {w : WeylGroup .E6} (hwδ : w • δ = δ) (hwθ : w • thetaE6 = thetaE6) :
    w ∈ kernelReflectionGroup (pairDiagE6 δ c) := by
  set v : RootSpace .E6 := ofLattice thetaE6 + (3 : ℝ) • ofLattice δ with hv
  have hstab : w ∈ weylStabilizer .E6 v := by
    change weylAct .E6 w v = v
    rw [hv, map_add, map_smul, weylAct_ofLattice, weylAct_ofLattice, hwθ, hwδ]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .E6).2.2.2.2.2 v] at hstab
  have hle : Subgroup.closure {s | ∃ α, IsRoot .E6 α ∧ inner ℝ (ofLattice α) v = 0 ∧
      s = rootReflection α} ≤ kernelReflectionGroup (pairDiagE6 δ c) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσ, hinner, rfl⟩
    obtain ⟨cc, hcc, hform⟩ := exists_inner_ofLattice_eq_iform .E6
    rw [hv, inner_add_right, inner_smul_right, hform, hform] at hinner
    have h1 : (iform σ thetaE6 : ℝ) + 3 * (iform σ δ : ℝ) = 0 := by
      have : cc * ((iform σ thetaE6 : ℝ) + 3 * (iform σ δ : ℝ)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hcc.ne'
      · exact h
    have h2 : iform σ thetaE6 + 3 * iform σ δ = 0 := by exact_mod_cast h1
    have b := abs_iform_thetaE6_le σ (mem_rootFinset.2 hσ)
    rw [iform_comm] at b
    rw [abs_le] at b
    have h3 : iform σ thetaE6 = 0 := by omega
    have h4 : iform σ δ = 0 := by omega
    refine rootReflection_mem_kernelReflectionGroup ⟨hσ, ?_⟩
    rw [rootChar_pairDiagE6, iform_comm δ σ, h4, iform_comm thetaE6 σ, h3]
    simp
  exact hle hstab

theorem rootCharStabilizer_pairDiagE6_le (hk : (-1 : kˣ) ≠ 1) {δ : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) (hδθ : iform thetaE6 δ = 0) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → c ^ j ≠ 1) {w : WeylGroup .E6}
    (hw : w ∈ rootCharStabilizer (pairDiagE6 δ c)) :
    w ∈ kernelReflectionGroup (pairDiagE6 δ c) := by
  classical
  have hbasis : ∀ j : Fin (Tag.rank .E6),
      iform thetaE6 (w • Pi.single j 1) = iform thetaE6 (Pi.single j 1) ∧
        Even (iform δ (w • Pi.single j 1) - iform δ (Pi.single j 1)) := by
    intro j
    have hroot : IsRoot .E6 (w • (Pi.single j 1 : Fin (Tag.rank .E6) → ℤ)) :=
      IsRoot.smul (isRoot_single _ j) w
    have h := hw (Pi.single j 1)
    rw [rootChar_pairDiagE6, rootChar_pairDiagE6] at h
    have b1 := abs_iform_thetaE6_le _ (mem_rootFinset.2 hroot)
    have b2 : iform thetaE6 (Pi.single j 1) = 0 ∨ iform thetaE6 (Pi.single j 1) = 1 := by
      rw [iform_thetaE6_single]
      split_ifs <;> simp
    rw [abs_le] at b1
    set x := iform δ (w • Pi.single j 1)
    set x' := iform δ (Pi.single j 1)
    set y := iform thetaE6 (w • Pi.single j 1)
    set y' := iform thetaE6 (Pi.single j 1)
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
  have hwθ : w • thetaE6 = thetaE6 := by
    set X := w⁻¹ • thetaE6 - thetaE6 with hX
    have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
      intro j
      have h1 := (hbasis j).1
      have h2 : iform thetaE6 (w • Pi.single j 1) = iform (w⁻¹ • thetaE6) (Pi.single j 1) := by
        rw [← iform_smul_smul w⁻¹ thetaE6 (w • Pi.single j 1), inv_smul_smul]
      rw [hX, iform_sub_left, ← h2, h1, sub_self]
    have hX0 : X = 0 := by
      by_contra hne
      have hpos := iform_self_pos hne
      rw [iform_eq_sum_single X X] at hpos
      simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
      exact lt_irrefl _ hpos
    have : w⁻¹ • thetaE6 = thetaE6 := sub_eq_zero.1 hX0
    calc w • thetaE6 = w • (w⁻¹ • thetaE6) := by rw [this]
      _ = thetaE6 := smul_inv_smul w _
  have hρ : w⁻¹ • δ = δ ∨ w⁻¹ • δ = -δ := by
    set ρ := w⁻¹ • δ with hρdef
    have hρroot : IsRoot .E6 ρ := IsRoot.smul hδ w⁻¹
    have hev : ∀ j, Even (iform (ρ - δ) (Pi.single j 1)) := by
      intro j
      have h2 : iform δ (w • Pi.single j 1) = iform ρ (Pi.single j 1) := by
        rw [← iform_smul_smul w⁻¹ δ (w • Pi.single j 1), inv_smul_smul]
      rw [iform_sub_left, ← h2]
      exact (hbasis j).2
    obtain ⟨Y, hY⟩ := exists_eq_two_smul_of_even_iform_single_E6 _ hev
    have hρρ := iform_self_isRoot_E6 hρroot
    have hδδ := iform_self_isRoot_E6 hδ
    have ht := abs_iform_le_two_E6 hρroot hδ
    rw [abs_le] at ht
    have hnorm : iform (ρ - δ) (ρ - δ) = 4 - 2 * iform ρ δ := by
      rw [iform_sub_left, iform_sub_right, iform_sub_right, hρρ, hδδ, iform_comm δ ρ]
      ring
    have hnorm2 : iform (ρ - δ) (ρ - δ) = 4 * iform Y Y := by
      rw [hY, two_nsmul, iform_add_left, iform_add_right]
      ring
    obtain ⟨m, hm⟩ := even_iform_self_E6 Y
    have hcases : iform ρ δ = 2 ∨ iform ρ δ = -2 := by omega
    rcases hcases with h2 | h2
    · left
      by_contra hne
      have := iform_self_pos (sub_ne_zero.2 hne)
      omega
    · right
      by_contra hne
      have hne' : ρ + δ ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
      have := iform_self_pos hne'
      rw [iform_add_left, iform_add_right, iform_add_right, hρρ, hδδ, iform_comm δ ρ] at this
      omega
  have hwδ : w • δ = δ ∨ w • δ = -δ := by
    rcases hρ with h | h
    · left
      calc w • δ = w • (w⁻¹ • δ) := by rw [h]
        _ = δ := smul_inv_smul w _
    · right
      have : w • (w⁻¹ • δ) = w • (-δ) := by rw [h]
      rw [smul_inv_smul, smul_neg] at this
      exact (neg_eq_iff_eq_neg.1 this.symm).symm ▸ rfl
  have hsδ : rootReflection δ • δ = -δ := rootReflection_smul_self hδ
  have hsθ : rootReflection δ • thetaE6 = thetaE6 :=
    rootReflection_smul_of_iform_eq_zero hδ (by rw [iform_comm]; exact hδθ)
  have hδker : δ ∈ rootCharKernel (pairDiagE6 δ c) := by
    refine ⟨hδ, ?_⟩
    rw [rootChar_pairDiagE6, iform_self_isRoot_E6 hδ, hδθ]
    simp
  rcases hwδ with h | h
  · exact mem_kernelReflectionGroup_of_fixes_E6 h hwθ
  · have h1 : (rootReflection δ * w) • δ = δ := by
      rw [mul_smul, h, smul_neg, hsδ, neg_neg]
    have h2 : (rootReflection δ * w) • thetaE6 = thetaE6 := by
      rw [mul_smul, hwθ, hsθ]
    have h3 := mem_kernelReflectionGroup_of_fixes_E6 (c := c) h1 h2
    have hs := rootReflection_mem_kernelReflectionGroup hδker
    have : w = rootReflection δ * (rootReflection δ * w) := by
      rw [← mul_assoc, rootReflection_mul_self hδ, one_mul]
    rw [this]
    exact mul_mem hs h3

end CFSG.ClassicalInvolution.ModelFacts.Levi
