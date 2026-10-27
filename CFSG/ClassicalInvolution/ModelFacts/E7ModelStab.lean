module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Descent

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.ClassicalInvolution.ModelFacts.Levi

variable {k : Type} [Field k]

theorem rootCharStabilizer_pairDiagE7_adj_le (hk : (-1 : kˣ) ≠ 1) {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : IsRoot .E7 δ) (hδθ : iform thetaE7 δ = 1 ∨ iform thetaE7 δ = -1) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → c ^ j ≠ 1) {w : WeylGroup .E7}
    (hw : w ∈ rootCharStabilizer (pairDiagE7 δ c)) :
    w ∈ kernelReflectionGroup (pairDiagE7 δ c) := by
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
      rw [Levi.iform_eq_sum_single X X] at hpos
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
      have h1 : iform thetaE7 (w • δ) = iform thetaE7 δ := by
        have := iform_smul_smul w thetaE7 δ
        rwa [hwθ] at this
      rw [h] at h1
      have h2 : iform thetaE7 (-δ) = -iform thetaE7 δ := by
        rw [show (-δ : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_right]
        ring
      rw [h2] at h1
      omega
  exact mem_kernelReflectionGroup_of_fixes_E7 hwδ hwθ

section Descent

theorem exists_levi_fixed_conj_E7_adj (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ)
    (hδθ : iform thetaE7 δ = 1 ∨ iform thetaE7 δ = -1) {y v : ModGL .E7 k}
    (hv : v ∈ parabolicLevi .E7 k JE7) (hFy : entrywiseFrobGL .E7 k p e y = y)
    (hvy : v * y * v⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1))) :
    ∃ h ∈ parabolicLevi .E7 k JE7, entrywiseFrobGL .E7 k p e h = h ∧
      h * y * h⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1)) := by
  classical
  have hchar : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set a' := pairDiagE7 δ c with ha'
  set d := rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) with hd
  set db := rootDiagUnit .E7 (thetaDiag thetaE7 c) with hdb
  have hsign : ∀ i, thetaDiag δ (-1 : kˣ) i = (1 : kˣ) ∨ thetaDiag δ (-1 : kˣ) i = -1 :=
    fun i => by
      rcases Int.even_or_odd (iform δ (Pi.single i 1)) with h | h
      · left; exact h.neg_one_zpow
      · right; exact h.neg_one_zpow
  have hFd : entrywiseFrobGL .E7 k p e d = d := entrywiseFrobGL_rootDiagUnit_of_sign p e hsign
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .E7 σ ∧ iform thetaE7 σ = 0 ∧
      rootChar (thetaDiag δ (-1 : kˣ)) σ = 1 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagE7_eq_one hc hσr hσ1
    exact ⟨hσr, h1, by rw [rootChar_thetaDiag]; exact h2⟩
  set M := torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (rootCharHom a')) with hM
  have hMd : ∀ m ∈ M, m * d * m⁻¹ = d := by
    have hle : M ≤ Subgroup.centralizer {d} := by
      refine sup_le (fun t ht => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
      · exact rootSpan_le_centralizer (thetaDiag δ (-1 : kˣ))
          (fun σ hσ => ⟨(hker σ hσ).1, (hker σ hσ).2.2⟩)
    intro m hm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hMJ : M ≤ parabolicLevi .E7 k JE7 := by
    refine sup_le (torusGroup_le_parabolicLevi JE7) ?_
    refine iSup₂_le fun σ hσ => rootSubgroup_le_parabolicLevi' ?_
    exact mem_parabolicRoots_E7 (hker σ hσ).1 (hker σ hσ).2.1
  have hlang : ∀ u ∈ M, ∃ m ∈ M, u = m⁻¹ * entrywiseFrobGL .E7 k p e m :=
    fun u hu => exists_eq_inv_mul_frob_torus_sup_rootSpan p he (rootCharHom a') hu
  have hFvJ : entrywiseFrobGL .E7 k p e v ∈ parabolicLevi .E7 k JE7 :=
    baseChangeGL_mem_parabolicLevi (iterateFrobenius k p e) hv
  have hu : entrywiseFrobGL .E7 k p e v * v⁻¹ ∈ M := by
    set u := entrywiseFrobGL .E7 k p e v * v⁻¹ with hudef
    have huJ : u ∈ parabolicLevi .E7 k JE7 := mul_mem hFvJ (inv_mem hv)
    have hF : entrywiseFrobGL .E7 k p e v * y * (entrywiseFrobGL .E7 k p e v)⁻¹ = d := by
      have := congrArg (entrywiseFrobGL .E7 k p e) hvy
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hud : d * u = u * d := by
      have hy' : v⁻¹ * d * v = y := by rw [← hvy]; group
      have h1 : u * d * u⁻¹ = d := by
        calc u * d * u⁻¹ = entrywiseFrobGL .E7 k p e v * (v⁻¹ * d * v) *
              (entrywiseFrobGL .E7 k p e v)⁻¹ := by rw [hudef]; group
          _ = d := by rw [hy', hF]
      calc d * u = (u * d * u⁻¹) * u := by rw [h1]
        _ = u * d := by group
    have hub : db * u = u * db := rootDiagUnit_thetaDiag_comm_levi_E7 c huJ
    have hmem : u ∈ toralCentralizer .E7 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JE7 huJ), ?_⟩
      have hmul : rootDiagUnit .E7 a' = d * db := rootDiagUnit_mul _ _
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * u = d * (db * u) := by group
        _ = d * (u * db) := by rw [hub]
        _ = (d * u) * db := by group
        _ = (u * d) * db := by rw [hud]
        _ = u * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiagE7_adj_le hk2 hδ hδθ hc hw) hmem
  obtain ⟨m, hm, hFix, hconj⟩ := exists_fixed_conj (entrywiseFrobGL .E7 k p e) hvy hMd hlang hu
  exact ⟨m * v, mul_mem (hMJ hm) hv, hFix, hconj⟩

end Descent

end CFSG.ClassicalInvolution.ModelFacts.E7Model
