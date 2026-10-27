module

public import CFSG.LieType.Chevalley.RootGramDet
public import CFSG.LieType.Chevalley.RootComponentType

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {τ : Tag} {n : ℕ}

theorem exists_mem_not_mem_span_of_compRank_lt {Ψ Ψ' : Set (Fin τ.rank → ℤ)}
    (h : compRank Ψ' < compRank Ψ) :
    ∃ δ ∈ Ψ, (fun i => (δ i : ℚ)) ∉
      Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ') := by
  by_contra hc
  push Not at hc
  have hle : Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ) ≤
      Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ') := by
    rw [Submodule.span_le]
    rintro _ ⟨δ, hδ, rfl⟩
    exact hc δ hδ
  have hfin := Submodule.finrank_mono hle
  unfold compRank at h
  omega


theorem exists_sum_smul_eq_zero_of_det_gram_eq_zero (D : Fin n → Fin τ.rank → ℤ)
    (h : (Matrix.of fun i j => iform (D i) (D j)).det = 0) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧ ∑ i, x i • D i = 0 := by
  classical
  obtain ⟨x, hx, hx0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine ⟨x, hx, ?_⟩
  by_contra hv
  have hsum : ∀ i, ∑ j, iform (D i) (D j) * x j = 0 := by
    intro i
    have h1 := congrFun hx0 i
    simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using h1
  have hvv : iform (∑ i, x i • D i) (∑ i, x i • D i) =
      ∑ i, x i * (∑ j, iform (D i) (D j) * x j) := by
    rw [iform_finset_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iform_smul_left, iform_finset_sum_right]
    simp only [Finset.mul_sum, iform_smul_right]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hzero : iform (∑ i, x i • D i) (∑ i, x i • D i) = 0 := by
    rw [hvv]
    exact Finset.sum_eq_zero fun i _ => by rw [hsum i, mul_zero]
  have := iform_self_pos hv
  omega

theorem exists_det_gram_eq_sq_mul {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (e : simpleRoots Ψ ≃ Fin n) (D : Fin n → Fin τ.rank → ℤ) (hD : ∀ i, D i ∈ Ψ) :
    ∃ m : ℤ, (Matrix.of fun i j => iform (D i) (D j)).det =
      m ^ 2 * (Matrix.of fun i j => iform ((e.symm i : simpleRoots Ψ) : Fin τ.rank → ℤ)
        ((e.symm j : simpleRoots Ψ) : Fin τ.rank → ℤ)).det := by
  classical
  have hc : ∀ i, ∃ c : (Fin τ.rank → ℤ) → ℤ, D i = ∑ β ∈ simpleRoots Ψ, c β • β :=
    fun i => exists_coords hΨ (hD i)
  choose c hc using hc
  refine ⟨Matrix.det (fun i j => c i (e.symm j)), ?_⟩
  have hM : ∀ i, D i = ∑ j, (fun i j => c i (e.symm j)) i j •
      ((fun j => ((e.symm j : simpleRoots Ψ) : Fin τ.rank → ℤ)) j) := by
    intro i
    rw [hc i, ← Finset.sum_coe_sort (simpleRoots Ψ)]
    exact (Equiv.sum_comp e.symm fun β : simpleRoots Ψ => c i β • (β : Fin τ.rank → ℤ)).symm
  exact det_gram_eq_det_sq_mul D (fun j => ((e.symm j : simpleRoots Ψ) : Fin τ.rank → ℤ))
    (fun i j => c i (e.symm j)) hM

theorem exists_A2_of_compRank_eq_two (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (h2 : compRank Ψ = 2) :
    ∃ α ∈ Ψ, ∃ β ∈ Ψ, iform α α = 2 ∧ iform β β = 2 ∧ iform α β = -1 := by
  classical
  have hne : Ψ.Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    subst h0
    have hz : compRank (∅ : Set (Fin τ.rank → ℤ)) = 0 := by simp [compRank]
    omega
  obtain ⟨t, e, ht, hsl, hiform, hcard⟩ := exists_dynkinType hτ hΨ hne
  have hrank : t.rank = 2 := by rw [← hcard.1, ← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ, h2]
  have htA : t = .A 2 := by
    rcases det_cartanMatrix_of_isSimplyLaced ht hsl with h | h | h | h | h
    · rw [h.1, hrank]
    · omega
    · exfalso
      rw [h.1, TauCeti.DynkinType.rank_E6] at hrank
      omega
    · exfalso
      rw [h.1, TauCeti.DynkinType.rank_E7] at hrank
      omega
    · exfalso
      rw [h.1, TauCeti.DynkinType.rank_E8] at hrank
      omega
  let i0 : Fin t.rank := Fin.cast hrank.symm 0
  let i1 : Fin t.rank := Fin.cast hrank.symm 1
  subst htA
  refine ⟨((e.symm i0 : simpleRoots Ψ) : Fin τ.rank → ℤ), simpleRoots_subset (e.symm i0).2,
    ((e.symm i1 : simpleRoots Ψ) : Fin τ.rank → ℤ), simpleRoots_subset (e.symm i1).2, ?_, ?_, ?_⟩
  · have h := hiform (e.symm i0) (e.symm i0)
    simp only [Equiv.apply_symm_apply] at h
    rw [h, TauCeti.DynkinType.cartanMatrix_A]
    rfl
  · have h := hiform (e.symm i1) (e.symm i1)
    simp only [Equiv.apply_symm_apply] at h
    rw [h, TauCeti.DynkinType.cartanMatrix_A]
    rfl
  · have h := hiform (e.symm i0) (e.symm i1)
    simp only [Equiv.apply_symm_apply] at h
    rw [h, TauCeti.DynkinType.cartanMatrix_A]
    rfl

private theorem gram_single_e6 :
    (Matrix.of fun i j => iform (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ)
      (Pi.single j 1)) = Tag.E6.cartan := by
  ext i j
  rw [Matrix.of_apply, iform_single_left]
  have hs : Tag.E6.symmetrizer i i = 1 := by simp [Tag.symmetrizer]
  rw [hs, one_mul, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, Ne.symm hb]
  · simp

private theorem det_gram_single_e6 :
    (Matrix.of fun i j => iform (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ)
      (Pi.single j 1)).det = 3 := by
  rw [gram_single_e6, det_cartan_E6]

private theorem three_mul_sq_ne (m : ℤ) {k : ℤ} (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 7) :
    m ^ 2 * 3 ≠ k := by
  intro h
  have h2 := congrArg (fun z : ℤ => (z : ZMod 3)) h
  push_cast at h2
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [h3, mul_zero] at h2
  rcases hk with rfl | rfl | rfl | rfl <;> revert h2 <;> decide

private theorem exists_det_gram_eq_sq_mul_three {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (e : simpleRoots Ψ ≃ Fin Tag.E6.rank) :
    ∃ m : ℤ, (Matrix.of fun i j => iform ((e.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)
      ((e.symm j : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)).det = m ^ 2 * 3 := by
  classical
  set D : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
    fun i => ((e.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ) with hD
  have hM : ∀ i, D i = ∑ j, (Matrix.of fun i j => D i j) i j •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
    intro i
    conv_lhs => rw [← Finset.univ_sum_single (D i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rfl
  refine ⟨(Matrix.of fun i j => D i j).det, ?_⟩
  have hdet := det_gram_eq_det_sq_mul D (fun j => (Pi.single j 1 : Fin Tag.E6.rank → ℤ))
    (Matrix.of fun i j => D i j) hM
  rw [hdet, det_gram_single_e6]

private theorem det_gram_eq_cartan_det {Ψ : Set (Fin Tag.E6.rank → ℤ)} (t : TauCeti.DynkinType)
    (e6 : simpleRoots Ψ ≃ Fin Tag.E6.rank) (e : simpleRoots Ψ ≃ Fin t.rank)
    (hiform : ∀ β γ : simpleRoots Ψ, iform (β : Fin Tag.E6.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ)) :
    (Matrix.of fun i j => iform ((e6.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)
      ((e6.symm j : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)).det = t.cartanMatrix.det := by
  have hG : (Matrix.of fun i j => iform ((e6.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)
      ((e6.symm j : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)) =
      t.cartanMatrix.submatrix (e6.symm.trans e) (e6.symm.trans e) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Equiv.trans_apply, hiform]
  rw [hG, Matrix.det_submatrix_equiv_self (e6.symm.trans e) t.cartanMatrix]

private theorem eq_E6_and_det_three_of_det_eq_sq_mul_three {t : TauCeti.DynkinType} (ht : t.Valid)
    (hsl : t.IsSimplyLaced) (hrank : t.rank = 6) {m : ℤ}
    (h : t.cartanMatrix.det = m ^ 2 * 3) : t = .E6 ∧ t.cartanMatrix.det = 3 := by
  rcases det_cartanMatrix_of_isSimplyLaced ht hsl with h' | h' | h' | h' | h'
  · exfalso
    have h1 : t.cartanMatrix.det = 7 := by rw [h'.2, hrank]; norm_num
    exact three_mul_sq_ne m (Or.inr (Or.inr (Or.inr rfl))) (by rw [← h, h1])
  · exfalso
    exact three_mul_sq_ne m (Or.inr (Or.inr (Or.inl rfl))) (by rw [← h, h'.2.2])
  · exact h'
  · exfalso
    exact three_mul_sq_ne m (Or.inr (Or.inl rfl)) (by rw [← h, h'.2])
  · exfalso
    exact three_mul_sq_ne m (Or.inl rfl) (by rw [← h, h'.2])

private theorem smul_mem_closure_of_adjugate {Ψ : Set (Fin τ.rank → ℤ)}
    (D D' : Fin n → Fin τ.rank → ℤ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i, D i = ∑ j, M i j • D' j) (hD : ∀ i, D i ∈ Ψ)
    (hm : M.det = 1 ∨ M.det = -1) (j : Fin n) : D' j ∈ AddSubgroup.closure Ψ := by
  have h := det_smul_eq_sum_adjugate D D' M hM j
  have hmem : M.det • D' j ∈ AddSubgroup.closure Ψ := by
    rw [h]
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hD i)) _
  rcases hm with hm | hm
  · rwa [hm, one_smul] at hmem
  · rw [hm, neg_one_smul] at hmem
    simpa using AddSubgroup.neg_mem _ hmem

private theorem exists_det_three_of_compRank_eq_six {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty) (h6 : compRank Ψ = 6) :
    ∃ e : simpleRoots Ψ ≃ Fin Tag.E6.rank,
      (Matrix.of fun i j => iform ((e.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)
        ((e.symm j : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)).det = 3 := by
  classical
  have hτ : (Tag.E6) = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inr (Or.inl rfl)
  obtain ⟨t, e, ht, hsl, hiform, hcard⟩ := exists_dynkinType hτ hΨ hne
  have hrank : t.rank = 6 := by
    rw [← hcard.1, ← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ, h6]
  let e6 : simpleRoots Ψ ≃ Fin Tag.E6.rank :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard.1, hrank]; rfl)
  obtain ⟨m, hm⟩ := exists_det_gram_eq_sq_mul_three hΨ e6
  have hdeq : t.cartanMatrix.det = m ^ 2 * 3 := by
    rw [← det_gram_eq_cartan_det t e6 e hiform, hm]
  obtain ⟨-, hdet3⟩ := eq_E6_and_det_three_of_det_eq_sq_mul_three ht hsl hrank hdeq
  refine ⟨e6, ?_⟩
  rw [det_gram_eq_cartan_det t e6 e hiform, hdet3]

private theorem exists_unit_matrix_of_det_three {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) {e : simpleRoots Ψ ≃ Fin Tag.E6.rank}
    (h3 : (Matrix.of fun i j => iform ((e.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)
      ((e.symm j : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)).det = 3) :
    ∃ M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ,
      (∀ i, ((e.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ) =
        ∑ j, M i j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ∧ (M.det = 1 ∨ M.det = -1) := by
  classical
  set D : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
    fun i => ((e.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ) with hD
  set M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := Matrix.of fun i j => D i j with hMdef
  have hM : ∀ i, D i = ∑ j, M i j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
    intro i
    conv_lhs => rw [← Finset.univ_sum_single (D i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rfl
  have hdet := det_gram_eq_det_sq_mul D (fun j => (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) M hM
  have hd3 : (Matrix.of fun i j => iform (D i) (D j)).det = 3 := h3
  have hm2 : M.det ^ 2 = 1 := by
    have h1 : M.det ^ 2 * 3 = 1 * 3 := by
      rw [show (1 : ℤ) * 3 = 3 by norm_num]
      calc M.det ^ 2 * 3 =
          M.det ^ 2 * (Matrix.of fun i j => iform (Pi.single i 1) (Pi.single j 1)).det := by
            rw [det_gram_single_e6]
        _ = (Matrix.of fun i j => iform (D i) (D j)).det := hdet.symm
        _ = 3 := hd3
    exact mul_right_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) h1
  have hmunit : M.det = 1 ∨ M.det = -1 := by
    have h3' : (M.det - 1) * (M.det + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 h3' with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  exact ⟨M, hM, hmunit⟩

theorem eq_setOf_isRoot_of_compRank_eq_six {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (h6 : compRank Ψ = 6) : Ψ = {α | IsRoot Tag.E6 α} := by
  classical
  refine Set.Subset.antisymm (fun α hα => hΨ.isRoot α hα) ?_
  have hne : Ψ.Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    subst h0
    have hz : compRank (∅ : Set (Fin Tag.E6.rank → ℤ)) = 0 := by simp [compRank]
    omega
  obtain ⟨e, h3⟩ := exists_det_three_of_compRank_eq_six hΨ hne h6
  obtain ⟨M, hM, hmunit⟩ := exists_unit_matrix_of_det_three hΨ h3
  have hD'mem : ∀ j, (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ AddSubgroup.closure Ψ := by
    intro j
    exact smul_mem_closure_of_adjugate
      (fun i => ((e.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ))
      (fun j => (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) M hM
      (fun i => simpleRoots_subset (e.symm i).2) hmunit j
  intro α hα
  have hmem : α ∈ AddSubgroup.closure Ψ := by
    rw [← Finset.univ_sum_single α]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    have h1 : (Pi.single j (α j) : Fin Tag.E6.rank → ℤ) = α j • Pi.single j 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [h1]
    exact AddSubgroup.zsmul_mem _ (hD'mem j) _
  exact mem_of_isRoot_mem_addClosure (Or.inr (Or.inl rfl)) hΨ.isRoot hΨ.neg_mem hΨ.add_mem hα hmem

end CFSG.LieType.Chevalley
