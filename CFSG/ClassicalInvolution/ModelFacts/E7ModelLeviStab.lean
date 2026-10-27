module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Data
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Stab
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.ClassicalInvolution.ModelFacts.Levi

variable {k : Type} [Field k]

@[expose] noncomputable def pairDiagG (δ l : Fin (Tag.rank .E7) → ℤ) (c : kˣ) :
    Fin (Tag.rank .E7) → kˣ :=
  thetaDiag δ (-1) * thetaDiag l c

theorem rootChar_pairDiagG (δ l v : Fin (Tag.rank .E7) → ℤ) (c : kˣ) :
    rootChar (pairDiagG δ l c) v = (-1 : kˣ) ^ iform δ v * c ^ iform l v := by
  rw [pairDiagG, rootChar_mul, rootChar_thetaDiag, rootChar_thetaDiag]

theorem iform_eq_zero_of_rootChar_pairDiagG_eq_one {B : ℕ} {l δ : Fin (Tag.rank .E7) → ℤ}
    (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 4 * B → c ^ j ≠ 1) {σ : Fin (Tag.rank .E7) → ℤ} (hσ : IsRoot .E7 σ)
    (h : rootChar (pairDiagG δ l c) σ = 1) :
    iform l σ = 0 ∧ (-1 : kˣ) ^ iform δ σ = 1 := by
  rw [rootChar_pairDiagG] at h
  have b := hB σ (mem_rootFinset.2 hσ)
  rw [abs_le] at b
  have hpow : ∀ n : ℤ, (c ^ n) ^ 2 = c ^ (2 * n) := fun n => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    norm_cast
  have h2 : ((-1 : kˣ) ^ iform δ σ * c ^ iform l σ) ^ 2 = 1 := by rw [h]; simp
  rw [mul_pow, neg_one_zpow_sq, one_mul, hpow] at h2
  have hy : iform l σ = 0 := by
    have := eq_zero_of_zpow_eq_one hc (m := 2 * iform l σ) (N := 4 * B) (by
      rw [abs_le]; omega) h2
    omega
  refine ⟨hy, ?_⟩
  rw [hy, zpow_zero, mul_one] at h
  exact h


section Weyl

variable {B : ℕ} {l δ : Fin (Tag.rank .E7) → ℤ}

theorem smul_eq_self_of_iform_single {w : WeylGroup .E7}
    (h : ∀ j : Fin (Tag.rank .E7), iform l (w • Pi.single j 1) = iform l (Pi.single j 1)) :
    w • l = l := by
  set X := w⁻¹ • l - l with hX
  have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
    intro j
    have h2 : iform l (w • Pi.single j 1) = iform (w⁻¹ • l) (Pi.single j 1) := by
      rw [← iform_smul_smul w⁻¹ l (w • Pi.single j 1), inv_smul_smul]
    rw [hX, iform_sub_left, ← h2, h j, sub_self]
  have hX0 : X = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [Levi.iform_eq_sum_single X X] at hpos
    simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  have : w⁻¹ • l = l := sub_eq_zero.1 hX0
  calc w • l = w • (w⁻¹ • l) := by rw [this]
    _ = l := smul_inv_smul w _

theorem mem_kernelReflectionGroup_of_fixes_G (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hδ : IsRoot .E7 δ) {c : kˣ} {w : WeylGroup .E7} (hwδ : w • δ = δ) (hwl : w • l = l) :
    w ∈ kernelReflectionGroup (pairDiagG δ l c) := by
  set v : RootSpace .E7 := ofLattice l + ((B + 1 : ℕ) : ℝ) • ofLattice δ with hv
  have hstab : w ∈ weylStabilizer .E7 v := by
    change weylAct .E7 w v = v
    rw [hv, map_add, map_smul, weylAct_ofLattice, weylAct_ofLattice, hwl, hwδ]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .E7).2.2.2.2.2 v] at hstab
  have hle : Subgroup.closure {s | ∃ α, IsRoot .E7 α ∧ inner ℝ (ofLattice α) v = 0 ∧
      s = rootReflection α} ≤ kernelReflectionGroup (pairDiagG δ l c) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσ, hinner, rfl⟩
    obtain ⟨cc, hcc, hform⟩ := exists_inner_ofLattice_eq_iform .E7
    rw [hv, inner_add_right, inner_smul_right, hform, hform] at hinner
    have h1 : (iform σ l : ℝ) + ((B + 1 : ℕ) : ℝ) * (iform σ δ : ℝ) = 0 := by
      have : cc * ((iform σ l : ℝ) + ((B + 1 : ℕ) : ℝ) * (iform σ δ : ℝ)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hcc.ne'
      · exact h
    have h2 : iform σ l + ((B + 1 : ℕ) : ℤ) * iform σ δ = 0 := by exact_mod_cast h1
    have b := hB σ (mem_rootFinset.2 hσ)
    rw [iform_comm] at b
    rw [abs_le] at b
    have b' := abs_iform_le_two_E7 hσ hδ
    rw [abs_le] at b'
    have h3 : iform σ δ = 0 := by
      have hz : iform σ δ = -2 ∨ iform σ δ = -1 ∨ iform σ δ = 0 ∨ iform σ δ = 1 ∨
          iform σ δ = 2 := by omega
      rcases hz with h | h | h | h | h <;> rw [h] at h2 <;> push_cast at h2 <;> omega
    have h4 : iform σ l = 0 := by
      rw [h3] at h2
      simpa using h2
    refine rootReflection_mem_kernelReflectionGroup ⟨hσ, ?_⟩
    rw [rootChar_pairDiagG, iform_comm δ σ, h3, iform_comm l σ, h4]
    simp
  exact hle hstab


theorem rootCharStabilizer_pairDiagG_le (hk : (-1 : kˣ) ≠ 1)
    (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B) (hδ : IsRoot .E7 δ) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 4 * B → c ^ j ≠ 1) {w : WeylGroup .E7}
    (hw : w ∈ rootCharStabilizer (pairDiagG δ l c)) :
    w ∈ kernelReflectionGroup (pairDiagG δ l c) := by
  classical
  have hbasis : ∀ j : Fin (Tag.rank .E7),
      iform l (w • Pi.single j 1) = iform l (Pi.single j 1) ∧
        Even (iform δ (w • Pi.single j 1) - iform δ (Pi.single j 1)) := by
    intro j
    have hroot : IsRoot .E7 (w • (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ)) :=
      IsRoot.smul (isRoot_single _ j) w
    have h := hw (Pi.single j 1)
    rw [rootChar_pairDiagG, rootChar_pairDiagG] at h
    have b1 := hB _ (mem_rootFinset.2 hroot)
    have b2 := hB (Pi.single j 1) (mem_rootFinset.2 (isRoot_single _ j))
    rw [abs_le] at b1 b2
    set x := iform δ (w • Pi.single j 1)
    set x' := iform δ (Pi.single j 1)
    set y := iform l (w • Pi.single j 1)
    set y' := iform l (Pi.single j 1)
    have hpow : ∀ n : ℤ, (c ^ n) ^ 2 = c ^ (2 * n) := fun n => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
      norm_cast
    have h2 : ((-1 : kˣ) ^ x * c ^ y) ^ 2 = ((-1 : kˣ) ^ x' * c ^ y') ^ 2 := by rw [h]
    rw [mul_pow, mul_pow, neg_one_zpow_sq, neg_one_zpow_sq, one_mul, one_mul, hpow, hpow] at h2
    have h3 : c ^ (2 * (y - y')) = 1 := by
      rw [mul_sub, zpow_sub, h2, mul_inv_cancel]
    have hyy : y = y' := by
      have := eq_zero_of_zpow_eq_one hc (m := 2 * (y - y')) (N := 4 * B) (by
        rw [abs_le]; omega) h3
      omega
    refine ⟨hyy, ?_⟩
    rw [hyy] at h
    have h4 : (-1 : kˣ) ^ x = (-1 : kˣ) ^ x' := mul_right_cancel h
    have h5 : (-1 : kˣ) ^ (x - x') = 1 := by rw [zpow_sub, h4, mul_inv_cancel]
    by_contra he
    have h6 : (-1 : kˣ) ^ (x - x') = -1 := by rw [neg_one_zpow_eq_ite]; simp [he]
    exact hk (h6.symm.trans h5)
  have hwl : w • l = l := smul_eq_self_of_iform_single fun j => (hbasis j).1
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
  rcases hwδ with h | h
  · exact mem_kernelReflectionGroup_of_fixes_G hB hδ h hwl
  · have hlδ : iform l δ = 0 := by
      have h1 : iform l (w • δ) = iform l δ := by
        have := iform_smul_smul w l δ
        rwa [hwl] at this
      rw [h] at h1
      have h2 : iform l (-δ) = -iform l δ := by
        rw [show (-δ : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_right]
        ring
      omega
    have hsδ : rootReflection δ • δ = -δ := rootReflection_smul_self hδ
    have hsl : rootReflection δ • l = l :=
      CFSG.LieType.Chevalley.rootReflection_smul_of_iform_eq_zero hδ
        (by rw [iform_comm]; exact hlδ)
    have hδker : δ ∈ rootCharKernel (pairDiagG δ l c) := by
      refine ⟨hδ, ?_⟩
      rw [rootChar_pairDiagG, iform_self_isRoot_E7 hδ, hlδ]
      simp
    have h1 : (rootReflection δ * w) • δ = δ := by
      rw [mul_smul, h, smul_neg, hsδ, neg_neg]
    have h2 : (rootReflection δ * w) • l = l := by
      rw [mul_smul, hwl, hsl]
    have h3 := mem_kernelReflectionGroup_of_fixes_G (c := c) hB hδ h1 h2
    have hs := rootReflection_mem_kernelReflectionGroup hδker
    have : w = rootReflection δ * (rootReflection δ * w) := by
      rw [← mul_assoc, rootReflection_mul_self hδ, one_mul]
    rw [this]
    exact mul_mem hs h3


theorem rootCharStabilizer_thetaDiag_le (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * B → c ^ j ≠ 1) {w : WeylGroup .E7}
    (hw : w ∈ rootCharStabilizer (thetaDiag l c)) :
    w ∈ kernelReflectionGroup (thetaDiag l c) := by
  classical
  have hbasis : ∀ j : Fin (Tag.rank .E7),
      iform l (w • Pi.single j 1) = iform l (Pi.single j 1) := by
    intro j
    have hroot : IsRoot .E7 (w • (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ)) :=
      IsRoot.smul (isRoot_single _ j) w
    have h := hw (Pi.single j 1)
    rw [rootChar_thetaDiag, rootChar_thetaDiag] at h
    have b1 := hB _ (mem_rootFinset.2 hroot)
    have b2 := hB (Pi.single j 1) (mem_rootFinset.2 (isRoot_single _ j))
    rw [abs_le] at b1 b2
    have h3 : c ^ (iform l (w • Pi.single j 1) - iform l (Pi.single j 1)) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    have := eq_zero_of_zpow_eq_one hc
      (m := iform l (w • Pi.single j 1) - iform l (Pi.single j 1)) (N := 2 * B) (by
        rw [abs_le]; omega) h3
    omega
  have hwl : w • l = l := smul_eq_self_of_iform_single hbasis
  have hstab : w ∈ weylStabilizer .E7 (ofLattice l) := by
    change weylAct .E7 w (ofLattice l) = ofLattice l
    rw [weylAct_ofLattice, hwl]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .E7).2.2.2.2.2 (ofLattice l)] at hstab
  have hle : Subgroup.closure {s | ∃ α, IsRoot .E7 α ∧ inner ℝ (ofLattice α) (ofLattice l) = 0 ∧
      s = rootReflection α} ≤ kernelReflectionGroup (thetaDiag l c) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσ, hinner, rfl⟩
    obtain ⟨cc, hcc, hform⟩ := exists_inner_ofLattice_eq_iform .E7
    rw [hform] at hinner
    have h1 : (iform σ l : ℝ) = 0 := by
      rcases mul_eq_zero.1 hinner with h | h
      · exact absurd h hcc.ne'
      · exact h
    have h2 : iform σ l = 0 := by exact_mod_cast h1
    refine rootReflection_mem_kernelReflectionGroup ⟨hσ, ?_⟩
    rw [rootChar_thetaDiag, iform_comm l σ, h2]
    simp
  exact hle hstab

theorem toralCentralizer_thetaDiag_le_levi {J : Set (Fin (Tag.rank .E7))}
    (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * B → c ^ j ≠ 1) :
    toralCentralizer .E7 k (thetaDiag l c) ≤ parabolicLevi .E7 k J := by
  intro g hg
  have hM := toralCentralizer_le_toralRootGroup (thetaDiag l c)
    (fun w hw => rootCharStabilizer_thetaDiag_le hB hc hw) hg
  refine (sup_le (torusGroup_le_parabolicLevi J) (iSup₂_le fun σ hσ =>
    rootSubgroup_le_parabolicLevi' ?_)) hM
  obtain ⟨hσr, hσ1⟩ := hσ
  rw [rootChar_thetaDiag] at hσ1
  have b := hB σ (mem_rootFinset.2 hσr)
  rw [abs_le] at b
  have h0 := eq_zero_of_zpow_eq_one hc (m := iform l σ) (N := 2 * B) (by
    rw [abs_le]; omega) hσ1
  exact hker σ (mem_rootFinset.2 hσr) h0

end Weyl

end CFSG.ClassicalInvolution.ModelFacts.E7Model
