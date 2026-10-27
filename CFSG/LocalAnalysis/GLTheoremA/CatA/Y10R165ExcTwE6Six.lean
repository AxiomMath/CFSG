module

public import CFSG.HardMathSupport.Lang.TwE6Step3.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3 CFSG.RankThree.PartOne.KE6
open scoped Matrix

@[expose] def tw6SixZx (p q : ℕ) : Fin Tag.E6.rank → ZMod p :=
  ![-1, (q : ZMod p) - 1, 0, 0, 1, 0]

@[expose] def tw6SixZy (p q : ℕ) : Fin Tag.E6.rank → ZMod p :=
  ![(q : ZMod p) - 1, 0, 0, 0, 0, 1]

private theorem one_eq_sub_sq {p q : ℕ} (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    (1 : ZMod p) = (q : ZMod p) - (q : ZMod p) ^ 2 := by
  have h : ((q : ZMod p) ^ 2 - (q : ZMod p) + 1) +
      ((q : ZMod p) - (q : ZMod p) ^ 2) = 1 := by ring
  rw [← h, hq, zero_add]

theorem tw6SixZx_mulVec (p q : ℕ) (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    (dualMatrix (ZMod p) e6T3W) *ᵥ tw6SixZx p q = (-(q : ZMod p)) • tw6SixZx p q := by
  rw [dualMatrix_e6T3W]
  change ((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZx p q)
    = (-(q : ZMod p)) • (tw6SixZx p q)
  funext i
  revert i
  change ∀ i : Fin 6,
    (((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZx p q)) i
      = ((-(q : ZMod p)) • (tw6SixZx p q)) i
  intro i
  fin_cases i <;>
    change (((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZx p q)) _
      = (-(q : ZMod p)) * tw6SixZx p q _ <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, e6T3Matrix6, tw6SixZx] <;>
    try ring
  exact one_eq_sub_sq hq

theorem tw6SixZy_mulVec (p q : ℕ) (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    (dualMatrix (ZMod p) e6T3W) *ᵥ tw6SixZy p q = (-(q : ZMod p)) • tw6SixZy p q := by
  rw [dualMatrix_e6T3W]
  change ((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZy p q)
    = (-(q : ZMod p)) • (tw6SixZy p q)
  funext i
  revert i
  change ∀ i : Fin 6,
    (((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZy p q)) i
      = ((-(q : ZMod p)) • (tw6SixZy p q)) i
  intro i
  fin_cases i <;>
    change (((e6T3Matrix6.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (tw6SixZy p q)) _
      = (-(q : ZMod p)) * tw6SixZy p q _ <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, e6T3Matrix6, tw6SixZy] <;>
    try ring
  exact one_eq_sub_sq hq

private def tw6SixNorm (α : Fin Tag.E6.rank → ℤ) : ℤ :=
  α (e6Index 1) ^ 2 + α (e6Index 1) * (α (e6Index 4) - α (e6Index 0) - α (e6Index 1)) +
    (α (e6Index 4) - α (e6Index 0) - α (e6Index 1)) ^ 2

private theorem tw6SixNorm_cases :
    ∀ m : Fin 72,
      (e6RootVec m (e6Index 1) = 0 ∧ e6RootVec m (e6Index 0) = e6RootVec m (e6Index 4)) ∨
      tw6SixNorm (e6RootVec m) = 1 ∨ tw6SixNorm (e6RootVec m) = 3 := by
  decide

theorem tw6SixZx_charVal (p q : ℕ) (α : Fin Tag.E6.rank → ℤ) :
    charVal (tw6SixZx p q) α =
      ((α (e6Index 1) : ℤ) : ZMod p) * (q : ZMod p) +
        (((α (e6Index 4) - α (e6Index 0) - α (e6Index 1) : ℤ)) : ZMod p) := by
  rw [charVal]
  change (∑ i : Fin 6, ((α (e6Index i) : ℤ) : ZMod p) * tw6SixZx p q (e6Index i)) = _
  rw [Fin.sum_univ_six]
  simp [tw6SixZx, e6Index]
  push_cast
  ring

theorem tw6SixZx_charVal_eq_zero_iff {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) :
    charVal (tw6SixZx p q) α = 0 ↔ α (e6Index 1) = 0 ∧ α (e6Index 0) = α (e6Index 4) := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
  have hp3 : 3 < p := by have := (Fact.out : p.Prime).two_le; omega
  have hnorm_ne : ∀ N : ℤ, N = 1 ∨ N = 3 → ((N : ℤ) : ZMod p) ≠ 0 := by
    rintro N (rfl | rfl)
    · norm_num
    · intro h
      have h' : (p : ℤ) ∣ 3 := (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).1 h
      have := Int.le_of_dvd (by norm_num) h'
      have hp5' : (5 : ℤ) < p := by exact_mod_cast hp5
      omega
  constructor
  · intro h0
    have hkey := tw6SixNorm_cases m
    set A : ℤ := e6RootVec m (e6Index 1) with hA
    set B : ℤ := e6RootVec m (e6Index 4) - e6RootVec m (e6Index 0) - e6RootVec m (e6Index 1)
      with hB
    have hNB : tw6SixNorm (e6RootVec m) = A ^ 2 + A * B + B ^ 2 := by
      simp only [tw6SixNorm, hA, hB]
    have hconj : (q : ZMod p) * (1 - (q : ZMod p)) = 1 := by linear_combination -hq
    have hnorm : (((A : ZMod p) * (q : ZMod p) + (B : ZMod p)) *
        ((A : ZMod p) * (1 - (q : ZMod p)) + (B : ZMod p))) =
          ((A ^ 2 + A * B + B ^ 2 : ℤ) : ZMod p) := by
      push_cast
      linear_combination ((A : ZMod p) ^ 2) * hconj
    have h0' : (A : ZMod p) * (q : ZMod p) + (B : ZMod p) = 0 := by
      rw [← tw6SixZx_charVal]
      exact h0
    have hnorm0 : ((A ^ 2 + A * B + B ^ 2 : ℤ) : ZMod p) = 0 := by
      rw [← hnorm, h0', zero_mul]
    rcases hkey with h | h | h
    · exact ⟨h.1, h.2⟩
    · rw [h] at hNB
      rw [← hNB] at hnorm0
      exact absurd hnorm0 (hnorm_ne 1 (Or.inl rfl))
    · rw [h] at hNB
      rw [← hNB] at hnorm0
      exact absurd hnorm0 (hnorm_ne 3 (Or.inr rfl))
  · rintro ⟨h1, h04⟩
    rw [tw6SixZx_charVal, h1]
    have h04' : e6RootVec m (e6Index 4) = e6RootVec m (e6Index 0) := h04.symm
    rw [h04']
    simp

@[expose] def tw6SixSupportA2 : Set (Fin Tag.E6.rank) :=
  ↑({e6Index 2, e6Index 3} : Finset (Fin Tag.E6.rank))

theorem tw6SixSupportA2_isA2Kernel :
    IsA2Kernel (parabolicRoots Tag.E6 tw6SixSupportA2) := by
  obtain ⟨w, hw⟩ := exists_smul_pair_eq ({e6Index 2, e6Index 3} : Finset (Fin Tag.E6.rank))
    (Or.inr (Or.inl rfl))
  exact ⟨w, hw⟩

theorem tw6SixSupportA2_subset_rootKernel_zx {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    parabolicRoots Tag.E6 tw6SixSupportA2 ⊆ rootKernel (tw6SixZx p q) := by
  intro α hα
  rw [mem_rootKernel]
  refine ⟨hα.1, (tw6SixZx_charVal_eq_zero_iff hp5 hq hα.1).2 ⟨?_, ?_⟩⟩
  · have h : (e6Index 1 : Fin Tag.E6.rank) ∉ tw6SixSupportA2 := by
      rw [tw6SixSupportA2, Finset.mem_coe, e6Index]
      decide
    exact hα.2 _ h
  · have h0 : (e6Index 0 : Fin Tag.E6.rank) ∉ tw6SixSupportA2 := by
      rw [tw6SixSupportA2, Finset.mem_coe, e6Index]
      decide
    have h4 : (e6Index 4 : Fin Tag.E6.rank) ∉ tw6SixSupportA2 := by
      rw [tw6SixSupportA2, Finset.mem_coe, e6Index]
      decide
    rw [hα.2 _ h0, hα.2 _ h4]

theorem tw6SixZy_charVal (p q : ℕ) (α : Fin Tag.E6.rank → ℤ) :
    charVal (tw6SixZy p q) α =
      ((α (e6Index 0) : ℤ) : ZMod p) * ((q : ZMod p) - 1) +
        ((α (e6Index 5) : ℤ) : ZMod p) := by
  rw [charVal]
  change (∑ i : Fin 6, ((α (e6Index i) : ℤ) : ZMod p) * tw6SixZy p q (e6Index i)) = _
  rw [Fin.sum_univ_six]
  simp [tw6SixZy, e6Index]

theorem tw6SixSupportA2_subset_rootKernel_zy {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    parabolicRoots Tag.E6 tw6SixSupportA2 ⊆ rootKernel (tw6SixZy p q) := by
  intro α hα
  rw [mem_rootKernel]
  refine ⟨hα.1, ?_⟩
  have h0 : α (e6Index 0) = 0 := by
    have h : (e6Index 0 : Fin Tag.E6.rank) ∉ tw6SixSupportA2 := by
      rw [tw6SixSupportA2, Finset.mem_coe, e6Index]
      decide
    exact hα.2 _ h
  have h5 : α (e6Index 5) = 0 := by
    have h : (e6Index 5 : Fin Tag.E6.rank) ∉ tw6SixSupportA2 := by
      rw [tw6SixSupportA2, Finset.mem_coe, e6Index]
      decide
    exact hα.2 _ h
  rw [tw6SixZy_charVal, h0, h5]
  ring

private def tw6SixA2A2Finset : Finset (Fin Tag.E6.rank) :=
  {e6Index 0, e6Index 2, e6Index 4, e6Index 5}

private theorem tw6SixA2A2Finset_coe :
    (↑tw6SixA2A2Finset : Set (Fin Tag.E6.rank)) = supportA2A2 := by
  ext i
  fin_cases i <;> simp [tw6SixA2A2Finset, supportA2A2]

private theorem tw6Six_support_eq_of_ncard (S : Finset (Fin Tag.E6.rank))
    (hS : S ∈ e6T3Supports) (h : (parabolicRoots Tag.E6 ↑S).ncard = 12) :
    S = tw6SixA2A2Finset := by
  simp only [e6T3Supports, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e6T3_parabolic_card] at h; revert h; decide
  · rw [e6T3_parabolic_card] at h; revert h; decide
  · rw [e6T3_parabolic_card] at h; revert h; decide
  · rw [e6T3_parabolic_card] at h; revert h; decide
  · rw [e6T3_parabolic_card] at h; revert h; decide
  · rw [e6T3_parabolic_card] at h; revert h; decide
  · rfl
  · rw [e6T3_parabolic_card] at h; revert h; decide

theorem ncard_rootKernel_tw6SixZx {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    (rootKernel (tw6SixZx p q)).ncard = 12 := by
  have hset : rootKernel (tw6SixZx p q) =
      e6RootVec '' ↑(Finset.univ.filter fun m : Fin 72 =>
        e6RootVec m (e6Index 1) = 0 ∧ e6RootVec m (e6Index 0) = e6RootVec m (e6Index 4)) := by
    ext α
    constructor
    · intro hα
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
      refine ⟨m, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (tw6SixZx_charVal_eq_zero_iff hp5 hq (isRoot_e6RootVec m)).1 hα.2⟩
    · rintro ⟨m, hm, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter] at hm
      exact ⟨isRoot_e6RootVec m,
        (tw6SixZx_charVal_eq_zero_iff hp5 hq (isRoot_e6RootVec m)).2 hm.2⟩
  rw [hset, Set.ncard_image_of_injective _ e6RootVec_injective, Set.ncard_coe_finset]
  decide

theorem tw6SixZx_isA2A2Kernel {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    IsA2A2Kernel (rootKernel (tw6SixZx p q)) := by
  have hz : tw6SixZx p q ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : Fin Tag.E6.rank)
    simp [tw6SixZx] at h0
  obtain ⟨u, S, hS, himg, -⟩ := e6T3_classification hp5 (tw6SixZx p q) hz (-(q : ZMod p))
    (tw6SixZx_mulVec p q hq)
  have h12 : (parabolicRoots Tag.E6 ↑S).ncard = 12 := by
    rw [← himg, Set.ncard_image_of_injective _ (MulAction.injective u)]
    exact ncard_rootKernel_tw6SixZx hp5 hq
  refine ⟨u, ?_⟩
  rw [himg, tw6Six_support_eq_of_ncard S hS h12, tw6SixA2A2Finset_coe]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
