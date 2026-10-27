module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

theorem flagSpace_eq_span_range (i : ℕ) :
    flagSpace n K i =
      Submodule.span K (Set.range fun j : {j : Fin n // (j : ℕ) < i} =>
        (Pi.single j.1 (1 : K) : Fin n → K)) := by
  rw [flagSpace]
  congr 1
  ext v
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.1, j.2, rfl⟩

theorem finrank_flagSpace {i : ℕ} (hi : i ≤ n) : finrank K (flagSpace n K i) = i := by
  have hli : LinearIndependent K (fun j : {j : Fin n // (j : ℕ) < i} =>
      (Pi.single j.1 (1 : K) : Fin n → K)) :=
    (Pi.linearIndependent_single_one (Fin n) K).comp _ Subtype.val_injective
  rw [flagSpace_eq_span_range, finrank_span_eq_card hli, Fintype.card_fin_lt_of_le hi]

theorem transvection_mulVec {i j : Fin n} (c : K) (v : Fin n → K) :
    transvection i j c *ᵥ v = v + Pi.single i (c * v j) := by
  rw [transvection, add_mulVec, one_mulVec, single_mulVec]
  rfl

theorem transvection_mem_unitriangular {i j : Fin n} (h : i < j) (c : K) :
    SpecialLinearGroup.transvection h.ne c ∈ unitriangular n K := by
  rw [mem_unitriangular, SpecialLinearGroup.transvection_coe]
  refine ⟨fun r s hrs => ?_, fun r => ?_⟩
  · rw [Matrix.add_apply, one_apply_ne hrs.ne', single_apply, ite_eq_right_iff.mpr, add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd (h.trans hrs) (lt_irrefl _)
  · rw [Matrix.add_apply, one_apply_eq, single_apply, ite_eq_right_iff.mpr, add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd h (lt_irrefl _)

theorem flagSpace_invariant (i : ℕ) {u : SpecialLinearGroup (Fin n) K}
    (hu : u ∈ upperTriangular n K) {v : Fin n → K} (hv : v ∈ flagSpace n K i) :
    (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ flagSpace n K i := by
  rw [mem_flagSpace] at hv ⊢
  intro k hk
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l k with hlk | hlk
  · rw [hu k l hlk, zero_mul]
  · rw [hv l (hk.trans hlk), mul_zero]

theorem eq_flagSpace_of_invariant {W : Submodule K (Fin n → K)}
    (hW : ∀ u ∈ unitriangular n K, ∀ v ∈ W, (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W) :
    ∃ m ≤ n, W = flagSpace n K m := by
  classical
  by_cases hbot : W = ⊥
  · exact ⟨0, Nat.zero_le _, by rw [hbot, flagSpace_zero]⟩
  set S : Finset (Fin n) := Finset.univ.filter fun j => ∃ v ∈ W, v j ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp hbot
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, hj⟩⟩
  set j₀ := S.max' hSne with hj₀
  have hj₀S : j₀ ∈ S := S.max'_mem hSne
  obtain ⟨v, hv, hvj⟩ := (Finset.mem_filter.mp hj₀S).2
  have hmax : ∀ w ∈ W, ∀ k : Fin n, j₀ < k → w k = 0 := fun w hw k hk => by
    by_contra hne
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, hne⟩
    exact absurd (S.le_max' k hkS) (not_le.mpr hk)
  have hlow : ∀ i : Fin n, i < j₀ → (Pi.single i (1 : K) : Fin n → K) ∈ W := by
    intro i hi
    have h1 := hW _ (transvection_mem_unitriangular hi 1) v hv
    rw [SpecialLinearGroup.transvection_coe, ← transvection, transvection_mulVec, one_mul] at h1
    have h2 : (Pi.single i (v j₀) : Fin n → K) ∈ W := by
      have := W.sub_mem h1 hv
      rwa [add_sub_cancel_left] at this
    have h3 := W.smul_mem (v j₀)⁻¹ h2
    rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hvj] at h3
  have htop : (Pi.single j₀ (1 : K) : Fin n → K) ∈ W := by
    have hsum : v = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j₀),
        Pi.single i (v i) + Pi.single j₀ (v j₀) := by
      ext k
      simp only [Pi.add_apply, Finset.sum_apply, Pi.single_apply]
      rw [Finset.sum_ite_eq]
      rcases lt_trichotomy k j₀ with hk | rfl | hk
      · simp [hk, hk.ne]
      · simp
      · simp [not_lt.mpr hk.le, hk.ne', hmax v hv k hk]
    have hrest : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j₀),
        (Pi.single i (v i) : Fin n → K) ∈ W := by
      refine W.sum_mem fun i hi => ?_
      have := W.smul_mem (v i) (hlow i (Finset.mem_filter.mp hi).2)
      rwa [← Pi.single_smul, smul_eq_mul, mul_one] at this
    have h2 : (Pi.single j₀ (v j₀) : Fin n → K) ∈ W := by
      have hB : (Pi.single j₀ (v j₀) : Fin n → K) =
          v - ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j₀), Pi.single i (v i) := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hsum.symm
      rw [hB]
      exact W.sub_mem hv hrest
    have h3 := W.smul_mem (v j₀)⁻¹ h2
    rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hvj] at h3
  refine ⟨j₀ + 1, j₀.isLt, le_antisymm ?_ ?_⟩
  · intro w hw
    rw [mem_flagSpace]
    intro k hk
    exact hmax w hw k (by rw [Fin.lt_def]; omega)
  · rw [flagSpace, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · exact hlow i (by rw [Fin.lt_def]; exact h)
    · rw [show i = j₀ from Fin.ext h]
      exact htop

theorem unitriangular_invariant_subspaces :
    (∀ W : Submodule K (Fin n → K),
      (∀ u ∈ unitriangular n K, ∀ v ∈ W, (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W) ↔
        ∃ m ≤ n, W = flagSpace n K m) ∧
    {v : Fin n → K | ∀ u ∈ unitriangular n K, (u : Matrix (Fin n) (Fin n) K) *ᵥ v = v} =
      (flagSpace n K 1 : Set (Fin n → K)) ∧
    ∀ V : Fin (n + 1) → Submodule K (Fin n → K), (∀ i, finrank K (V i) = i) →
      (∀ i, ∀ u ∈ unitriangular n K, ∀ v ∈ V i, (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ V i) →
        ∀ i, V i = flagSpace n K i := by
  refine ⟨fun W => ⟨eq_flagSpace_of_invariant, ?_⟩, ?_, ?_⟩
  · rintro ⟨m, -, rfl⟩ u hu v hv
    exact flagSpace_invariant m (unitriangular_le_upperTriangular n K hu) hv
  · ext v
    change (∀ u ∈ unitriangular n K, (u : Matrix (Fin n) (Fin n) K) *ᵥ v = v) ↔
      v ∈ flagSpace n K 1
    rw [mem_flagSpace]
    constructor
    · intro hv j hj
      have hj0 : (⟨0, by omega⟩ : Fin n) < j := by rw [Fin.lt_def]; simp; omega
      have h := hv _ (transvection_mem_unitriangular hj0 1)
      rw [SpecialLinearGroup.transvection_coe, ← transvection, transvection_mulVec, one_mul,
        add_eq_left] at h
      simpa using congrFun h ⟨0, by omega⟩
    · intro hv u hu
      ext k
      rw [mulVec, dotProduct]
      rw [Finset.sum_eq_single k]
      · rw [hu.2 k, one_mul]
      · intro l _ hlk
        rcases lt_or_gt_of_ne hlk with h | h
        · rw [hu.1 k l h, zero_mul]
        · rw [hv l (by rw [Fin.lt_def] at h; omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ k) h
  · intro V hdim hinv i
    obtain ⟨m, hm, hVm⟩ := eq_flagSpace_of_invariant (hinv i)
    have h := hdim i
    rw [hVm, finrank_flagSpace hm] at h
    rw [hVm, h]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
