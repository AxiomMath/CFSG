module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix Subgroup

variable {K : Type*} [Field K] {n : ℕ}

theorem flagSpace_succ_le {W : Submodule K (Fin n → K)} {i : Fin n}
    (hle : flagSpace n K i ≤ W) (hi : (Pi.single i (1 : K) : Fin n → K) ∈ W) :
    flagSpace n K ((i : ℕ) + 1) ≤ W := by
  rw [flagSpace, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
  · exact hle (Submodule.subset_span ⟨j, h, rfl⟩)
  · rw [show j = i from Fin.ext h]
    exact hi

theorem single_mem_of_lead {W : Submodule K (Fin n → K)} {i : Fin n}
    (hle : flagSpace n K i ≤ W) {w : Fin n → K} (hw : w ∈ W)
    (hwF : w ∈ flagSpace n K ((i : ℕ) + 1)) (hwi : w i ≠ 0) :
    (Pi.single i (1 : K) : Fin n → K) ∈ W := by
  have hrest : w - Pi.single i (w i) ∈ flagSpace n K i := by
    rw [mem_flagSpace] at hwF ⊢
    intro j hj
    rcases eq_or_ne j i with rfl | hne
    · simp
    · rw [Pi.sub_apply, Pi.single_eq_of_ne hne, sub_zero]
      exact hwF j (by have := Fin.val_ne_of_ne hne; omega)
  have h2 : (Pi.single i (w i) : Fin n → K) ∈ W := by
    have := W.sub_mem hw (hle hrest)
    rwa [sub_sub_cancel] at this
  have h3 := W.smul_mem (w i)⁻¹ h2
  rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hwi] at h3

theorem sub_mem_flagSpace {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ unitriangular n K)
    {i : ℕ} {w : Fin n → K} (hw : w ∈ flagSpace n K (i + 1 + 1)) :
    (u : Matrix (Fin n) (Fin n) K) *ᵥ w - w ∈ flagSpace n K (i + 1) := by
  rw [mem_flagSpace] at hw ⊢
  intro k hk
  rw [Pi.sub_apply, sub_eq_zero, mulVec, dotProduct, Finset.sum_eq_single k]
  · rw [hu.2 k, one_mul]
  · intro l _ hlk
    rcases lt_or_gt_of_ne hlk with h | h
    · rw [hu.1 k l h, zero_mul]
    · rw [hw l (by rw [Fin.lt_def] at h; omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem sub_apply_lead {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ unitriangular n K)
    {i j : Fin n} (hij : (j : ℕ) = i + 1) {w : Fin n → K}
    (hw : w ∈ flagSpace n K ((j : ℕ) + 1)) :
    ((u : Matrix (Fin n) (Fin n) K) *ᵥ w - w) i = (u : Matrix (Fin n) (Fin n) K) i j * w j := by
  rw [mem_flagSpace] at hw
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  rw [Pi.sub_apply, mulVec, dotProduct, Fintype.sum_eq_add i j hne]
  · rw [hu.2 i, one_mul, add_sub_cancel_left]
  · rintro l ⟨hli, hlj⟩
    have hlj' : (l : ℕ) ≠ j := fun h => hlj (Fin.ext h)
    rcases lt_or_gt_of_ne hli with h | h
    · rw [hu.1 i l h, zero_mul]
    · rw [hw l (by rw [Fin.lt_def] at h; omega), mul_zero]

theorem flagSpace_le_of_regular {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ unitriangular n K)
    (hreg : ∀ i j : Fin n, (j : ℕ) = i + 1 → (u : Matrix (Fin n) (Fin n) K) i j ≠ 0)
    {W : Submodule K (Fin n → K)} (hW : ∀ v ∈ W, (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W) :
    ∀ (i : ℕ) (hi : i < n) (w : Fin n → K), w ∈ W → w ∈ flagSpace n K (i + 1) →
      w ⟨i, hi⟩ ≠ 0 → flagSpace n K (i + 1) ≤ W := by
  intro i
  induction i with
  | zero =>
    intro hi w hw hwF hw0
    have h0 : flagSpace n K 0 ≤ W := by
      rw [flagSpace_zero]
      exact bot_le
    exact flagSpace_succ_le (i := ⟨0, hi⟩) h0 (single_mem_of_lead (i := ⟨0, hi⟩) h0 hw hwF hw0)
  | succ i ih =>
    intro hi w hw hwF hw0
    have hi' : i < n := by omega
    have hw'0 : ((u : Matrix (Fin n) (Fin n) K) *ᵥ w - w) ⟨i, hi'⟩ ≠ 0 := by
      rw [sub_apply_lead hu (i := ⟨i, hi'⟩) (j := ⟨i + 1, hi⟩) rfl hwF]
      exact mul_ne_zero (hreg _ _ rfl) hw0
    have hle := ih hi' _ (W.sub_mem (hW w hw) hw) (sub_mem_flagSpace hu hwF) hw'0
    exact flagSpace_succ_le (i := ⟨i + 1, hi⟩) hle
      (single_mem_of_lead (i := ⟨i + 1, hi⟩) hle hw hwF hw0)

theorem eq_flagSpace_of_regular {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ unitriangular n K)
    (hreg : ∀ i j : Fin n, (j : ℕ) = i + 1 → (u : Matrix (Fin n) (Fin n) K) i j ≠ 0)
    {W : Submodule K (Fin n → K)} (hW : ∀ v ∈ W, (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W) :
    ∃ m ≤ n, W = flagSpace n K m := by
  classical
  have htop : W ≤ flagSpace n K n := fun v _ =>
    mem_flagSpace.mpr fun j hj => absurd j.isLt (not_lt.mpr hj)
  have hex : ∃ m, W ≤ flagSpace n K m := ⟨n, htop⟩
  obtain ⟨m, hWm, hmin⟩ : ∃ m, W ≤ flagSpace n K m ∧ ∀ k < m, ¬ W ≤ flagSpace n K k :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hmn : m ≤ n := by
    by_contra h
    exact hmin n (by omega) htop
  rcases m with _ | j
  · exact ⟨0, Nat.zero_le _, le_antisymm hWm (by rw [flagSpace_zero]; exact bot_le)⟩
  · obtain ⟨w, hw, hwj⟩ := IsConcreteLE.not_le_iff_exists.mp (hmin j (Nat.lt_succ_self j))
    have hwF := hWm hw
    rw [mem_flagSpace] at hwj
    push Not at hwj
    obtain ⟨k, hjk, hk0⟩ := hwj
    have hkj : (k : ℕ) = j := by
      by_contra hne
      exact hk0 (mem_flagSpace.mp hwF k (by omega))
    have hj : j < n := hkj ▸ k.isLt
    have hk : k = ⟨j, hj⟩ := Fin.ext hkj
    rw [hk] at hk0
    exact ⟨j + 1, hmn, le_antisymm hWm (flagSpace_le_of_regular hu hreg hW j hj w hw hwF hk0)⟩

theorem mem_upperTriangular_of_regular {u g : SpecialLinearGroup (Fin n) K}
    (hu : u ∈ unitriangular n K)
    (hreg : ∀ i j : Fin n, (j : ℕ) = i + 1 → (u : Matrix (Fin n) (Fin n) K) i j ≠ 0)
    (hg : g⁻¹ * u * g ∈ unitriangular n K) : g ∈ upperTriangular n K := by
  rw [← flagFamilyStabilizer_standardFlag, mem_flagFamilyStabilizer]
  intro i
  have hinv : ∀ v ∈ (flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)),
      (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        (flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨((g⁻¹ * u * g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v,
      flagSpace_invariant i (unitriangular_le_upperTriangular n K hg) hv, ?_⟩
    rw [mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, ← SpecialLinearGroup.coe_mul,
      show g * (g⁻¹ * u * g) = u * g by group, SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
  obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_regular hu hreg hinv
  have hfin := congrArg (fun W : Submodule K (Fin n → K) => Module.finrank K W) hW
  rw [show Module.finrank K ((flagSpace n K i).map
      (mulVecLin (g : Matrix (Fin n) (Fin n) K))) = Module.finrank K (flagSpace n K i) from
      LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) _,
    finrank_flagSpace (by omega), finrank_flagSpace hm] at hfin
  rw [mem_stabilizer]
  change (flagSpace n K i).map _ = flagSpace n K i
  rw [hW, hfin]

theorem eq_unitriangular_of_regular_mem [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hn : 1 ≤ n) {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ unitriangular n K)
    (hreg : ∀ i j : Fin n, (j : ℕ) = i + 1 → (u : Matrix (Fin n) (Fin n) K) i j ≠ 0)
    (P : Sylow p (SpecialLinearGroup (Fin n) K)) (huP : u ∈ P) :
    (P : Subgroup (SpecialLinearGroup (Fin n) K)) = unitriangular n K := by
  obtain ⟨SU, hSU⟩ := exists_sylow_unitriangular (K := K) p hn
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) K) SU P
  have huP' : u ∈ ((x • SU : Sylow p _) : Subgroup (SpecialLinearGroup (Fin n) K)) := by
    rw [hx]
    exact huP
  rw [coe_sylow_smul, hSU] at huP'
  obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp huP'
  have hxu : x⁻¹ * u * x ∈ unitriangular n K := by
    rw [← hyu]
    simpa [mul_assoc] using hy
  have hxN : x ∈ normalizer ((SU : Subgroup (SpecialLinearGroup (Fin n) K)) :
      Set (SpecialLinearGroup (Fin n) K)) := by
    rw [hSU, normalizer_unitriangular]
    exact mem_upperTriangular_of_regular hu hreg hxu
  rw [← hx, Sylow.smul_eq_iff_mem_normalizer.mpr hxN, hSU]

theorem le_unitriangular_of_regular_mem [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hn : 1 ≤ n) {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ unitriangular n K)
    (hreg : ∀ i j : Fin n, (j : ℕ) = i + 1 → (u : Matrix (Fin n) (Fin n) K) i j ≠ 0)
    {Q : Subgroup (SpecialLinearGroup (Fin n) K)} (hQ : IsPGroup p Q) (huQ : u ∈ Q) :
    Q ≤ unitriangular n K := by
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  rw [← eq_unitriangular_of_regular_mem p hn hu hreg P (hQP huQ)]
  exact hQP

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
