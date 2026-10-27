module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplecticStrong

public section

namespace CFSG.QuasithinUnique.K1

open Matrix Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {K : Type} [Field K]

abbrev spM (g : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem spM_mul (g h : StatedSp 2 K) : spM (g * h) = spM g * spM h := rfl

theorem spM_symp (g : StatedSp 2 K) :
    (spM g)ᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * spM g =
      fromBlocks 0 1 (-1) 0 :=
  SymplecticTorusWeyl.mem_statedSp_iff.mp g.2

theorem spM_tauS_first (t : K) :
    spM (tauS t 0 0) =
      1 + t • single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) := by
  change ((((tauS t 0 0 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
  rw [coe_tauS]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [sym2]

@[expose] def ColZero (g : StatedSp 2 K) : Prop :=
  ∀ k : Fin 2 ⊕ Fin 2, k ≠ Sum.inl 0 → spM g k (Sum.inl 0) = 0

theorem colZero_of_mem_stabilizer {g : StatedSp 2 K}
    (hg : g ∈ stabilizer 2 K (flag 2 K 1)) : ColZero g := by
  intro k hk
  have hmem : (spM g *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) ∈ flag 2 K 1 := by
    have h1 : (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 := by
      rw [mem_flag_of_le (by norm_num)]
      exact Submodule.subset_span ⟨0, by simp, rfl⟩
    have h2 := (mem_stabilizer.mp hg)
    rw [← h2]
    exact ⟨_, h1, rfl⟩
  rw [mem_flag_of_le (by norm_num), mem_isoFlag] at hmem
  have hcol : ∀ k, (spM g *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) k =
      spM g k (Sum.inl 0) := fun k => by
    rw [mulVec_single_one]
    rfl
  rcases k with (k | k)
  · have hk1 : k = 1 := by
      fin_cases k
      · exact absurd rfl hk
      · rfl
    subst hk1
    have := hmem.2 1 le_rfl
    rw [hcol] at this
    exact this
  · have := hmem.1 k
    rw [hcol] at this
    exact this

theorem mem_stabilizer_of_colZero {g : StatedSp 2 K} (h : ColZero g) (h' : ColZero g⁻¹) :
    g ∈ stabilizer 2 K (flag 2 K 1) := by
  have key : ∀ g : StatedSp 2 K, ColZero g → ∀ v ∈ flag 2 K 1, spM g *ᵥ v ∈ flag 2 K 1 := by
    intro g hg v hv
    rw [mem_flag_of_le (by norm_num), mem_isoFlag] at hv ⊢
    obtain ⟨hv1, hv2⟩ := hv
    have hv' : ∀ m, m ≠ Sum.inl 0 → v m = 0 := by
      intro m hm
      rcases m with (m | m)
      · have hm1 : m = 1 := by
          fin_cases m
          · exact absurd rfl hm
          · rfl
        subst hm1
        exact hv2 1 le_rfl
      · exact hv1 m
    have hmv : ∀ k, (spM g *ᵥ v) k = spM g k (Sum.inl 0) * v (Sum.inl 0) := fun k => by
      rw [mulVec, dotProduct, Finset.sum_eq_single (Sum.inl 0)]
      · intro m _ hm
        rw [hv' m hm, mul_zero]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · rw [hmv, hg (Sum.inr j) (by simp), zero_mul]
    · have hj1 : j = 1 := by
        fin_cases j
        · exact absurd (Nat.le_zero.mp hj) (by simp)
        · rfl
      subst hj1
      rw [hmv, hg (Sum.inl 1) (by simp), zero_mul]
  exact mem_stabilizer_of_mulVec_mem (key g h) (key g⁻¹ h')

theorem sum_inl_zero_col {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : ∀ k : Fin 2 ⊕ Fin 2, k ≠ Sum.inl 0 → M k (Sum.inl 0) = 0) (f : Fin 2 ⊕ Fin 2 → K) :
    ∑ k, M k (Sum.inl 0) * f k = M (Sum.inl 0) (Sum.inl 0) * f (Sum.inl 0) := by
  rw [Finset.sum_eq_single (Sum.inl 0)]
  · intro k _ hk
    rw [h k hk, zero_mul]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

theorem lam_mul_row_matrix {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {μ : K}
    (h : ∀ k : Fin 2 ⊕ Fin 2, k ≠ Sum.inl 0 → M k (Sum.inl 0) = 0)
    (hsymp : Mᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * M =
      μ • fromBlocks 0 1 (-1) 0) (l : Fin 2 ⊕ Fin 2) :
    M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) l = μ * (if l = Sum.inr 0 then 1 else 0) := by
  have h1 := congrFun₂ hsymp (Sum.inl 0) l
  have hJ : ∀ m : Fin 2 ⊕ Fin 2, (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) m = if m = Sum.inr 0 then 1 else 0 := by
    intro m
    rcases m with (m | m)
    · simp
    · simp [Matrix.one_apply, eq_comm]
  have h2 : (Mᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      * M) (Sum.inl 0) l = M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) l := by
    rw [Matrix.mul_apply]
    have : ∀ m, (Mᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        (Sum.inl 0) m = M (Sum.inl 0) (Sum.inl 0) *
          (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) m := by
      intro m
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply]
      exact sum_inl_zero_col h (fun k => (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2)
        (Fin 2 ⊕ Fin 2) K) k m)
    simp only [this, hJ]
    rw [Finset.sum_eq_single (Sum.inr 0)]
    · simp
    · intro m _ hm
      simp [hm]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  rw [h1, Matrix.smul_apply, hJ, smul_eq_mul] at h2
  exact h2.symm

theorem lam_mul_row {g : StatedSp 2 K} (h : ColZero g) (l : Fin 2 ⊕ Fin 2) :
    spM g (Sum.inl 0) (Sum.inl 0) * spM g (Sum.inr 0) l = if l = Sum.inr 0 then 1 else 0 := by
  have := lam_mul_row_matrix (M := spM g) (μ := 1) h (by rw [one_smul]; exact spM_symp g) l
  rwa [one_mul] at this

theorem mul_single_eq {g : StatedSp 2 K} (h : ColZero g) :
    spM g * single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) =
      (spM g (Sum.inl 0) (Sum.inl 0)) ^ 2 •
        (single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) * spM g) := by
  ext k l
  rw [Matrix.smul_apply, smul_eq_mul]
  have hrow := lam_mul_row h l
  by_cases hl : l = Sum.inr 0
  · subst hl
    rw [mul_single_apply_same, mul_one]
    by_cases hk : k = Sum.inl 0
    · subst hk
      rw [single_mul_apply_same, one_mul]
      have hrow' : spM g (Sum.inl 0) (Sum.inl 0) * spM g (Sum.inr 0) (Sum.inr 0) = 1 := by
        simpa using hrow
      calc spM g (Sum.inl 0) (Sum.inl 0)
          = spM g (Sum.inl 0) (Sum.inl 0) * 1 := by rw [mul_one]
        _ = spM g (Sum.inl 0) (Sum.inl 0) *
            (spM g (Sum.inl 0) (Sum.inl 0) * spM g (Sum.inr 0) (Sum.inr 0)) := by rw [hrow']
        _ = (spM g (Sum.inl 0) (Sum.inl 0)) ^ 2 * spM g (Sum.inr 0) (Sum.inr 0) := by ring
    · rw [single_mul_apply_of_ne _ _ _ _ _ hk, mul_zero]
      exact h k hk
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl]
    by_cases hk : k = Sum.inl 0
    · subst hk
      rw [single_mul_apply_same, one_mul]
      have hrow' : spM g (Sum.inl 0) (Sum.inl 0) * spM g (Sum.inr 0) l = 0 := by
        simpa [hl] using hrow
      calc (0 : K) = spM g (Sum.inl 0) (Sum.inl 0) * 0 := by rw [mul_zero]
        _ = spM g (Sum.inl 0) (Sum.inl 0) *
            (spM g (Sum.inl 0) (Sum.inl 0) * spM g (Sum.inr 0) l) := by rw [hrow']
        _ = (spM g (Sum.inl 0) (Sum.inl 0)) ^ 2 * spM g (Sum.inr 0) l := by ring
    · rw [single_mul_apply_of_ne _ _ _ _ _ hk, mul_zero]

theorem exists_tauS_conj_of_mem_stabilizer {g : StatedSp 2 K}
    (hg : g ∈ stabilizer 2 K (flag 2 K 1)) : ∃ s : K, g * tauS 1 0 0 * g⁻¹ = tauS s 0 0 := by
  have h := colZero_of_mem_stabilizer hg
  refine ⟨(spM g (Sum.inl 0) (Sum.inl 0)) ^ 2, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply SymplecticTorusWeyl.statedSp_ext
  show spM (g * tauS 1 0 0) = spM (tauS _ 0 0 * g)
  rw [spM_mul, spM_mul, spM_tauS_first, spM_tauS_first, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, one_smul,
    mul_single_eq h]

theorem colZero_of_conj {g : StatedSp 2 K} {a s : K} (ha : a ≠ 0)
    (h : g * tauS a 0 0 * g⁻¹ = tauS s 0 0) : ColZero g := by
  rw [mul_inv_eq_iff_eq_mul] at h
  have h' := congrArg spM h
  rw [spM_mul, spM_mul, spM_tauS_first, spM_tauS_first, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul] at h'
  have h'' := add_left_cancel h'
  rw [Matrix.mul_smul, Matrix.smul_mul] at h''
  intro k hk
  have := congrFun₂ h'' k (Sum.inr 0)
  rw [Matrix.smul_apply, Matrix.smul_apply, mul_single_apply_same,
    single_mul_apply_of_ne _ _ _ _ _ hk] at this
  simpa [ha] using this

theorem mem_stabilizer_of_conj_tauS {g : StatedSp 2 K} {s : K}
    (h : g * tauS 1 0 0 * g⁻¹ = tauS s 0 0) : g ∈ stabilizer 2 K (flag 2 K 1) := by
  have hs : s ≠ 0 := by
    rintro rfl
    have h0 : g * tauS (1 : K) 0 0 * g⁻¹ = 1 := by rw [h, tauS_zero]
    have h1 : tauS (1 : K) 0 0 = 1 := by
      calc tauS (1 : K) 0 0 = g⁻¹ * (g * tauS (1 : K) 0 0 * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h0]
        _ = 1 := by group
    exact one_ne_zero (tauS_injective (h1.trans tauS_zero.symm)).1
  refine mem_stabilizer_of_colZero (colZero_of_conj one_ne_zero h)
    (colZero_of_conj (s := (1 : K)) hs ?_)
  rw [inv_inv, ← h]
  group

end CFSG.QuasithinUnique.K1
