module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Bruhat
public import Mathlib.LinearAlgebra.Matrix.Rank

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def cornerRank (g : Matrix (Fin n) (Fin n) K) (i j : ℕ) : ℕ :=
  (g.submatrix (fun r : {r : Fin n // i ≤ (r : ℕ) + 1} => (r : Fin n))
    (fun c : {c : Fin n // (c : ℕ) + 1 ≤ j} => (c : Fin n))).rank

@[expose] def cornerCount (w : Equiv.Perm (Fin n)) (i j : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin n => (a : ℕ) + 1 ≤ j ∧ i ≤ (w a : ℕ) + 1).card

@[expose] def bruhatCell (w : Equiv.Perm (Fin n)) : Set (SpecialLinearGroup (Fin n) K) :=
  DoubleCoset.doubleCoset (signedPermutation n K w) (upperTriangular n K) (upperTriangular n K)

theorem mem_bruhatCell {w : Equiv.Perm (Fin n)} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ bruhatCell w ↔ ∃ b₁ ∈ upperTriangular n K, ∃ b₂ ∈ upperTriangular n K,
      g = b₁ * signedPermutation n K w * b₂ :=
  DoubleCoset.mem_doubleCoset

theorem upperTriangular_apply_self_ne_zero {b : SpecialLinearGroup (Fin n) K}
    (hb : b ∈ upperTriangular n K) (r : Fin n) : (b : Matrix (Fin n) (Fin n) K) r r ≠ 0 := by
  have h := b.2
  rw [det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hb)] at h
  have h' : ∏ x, (b : Matrix (Fin n) (Fin n) K) x x ≠ 0 := by
    rw [h]
    exact one_ne_zero
  exact Finset.prod_ne_zero_iff.mp h' r (Finset.mem_univ r)

theorem isUnit_det_submatrix_of_isUpperTriangular {b : Matrix (Fin n) (Fin n) K}
    (hb : b.IsUpperTriangular) (hd : ∀ r, b r r ≠ 0) (p : Fin n → Prop) [DecidablePred p] :
    IsUnit (b.submatrix (fun r : {r // p r} => (r : Fin n))
      (fun r : {r // p r} => (r : Fin n))).det := by
  have htri : (b.submatrix (fun r : {r // p r} => (r : Fin n))
      (fun r : {r // p r} => (r : Fin n))).IsUpperTriangular := fun r s hrs => hb hrs
  rw [isUnit_iff_ne_zero, det_of_isUpperTriangular htri]
  exact Finset.prod_ne_zero_iff.mpr fun r _ => hd r

theorem cornerRank_mul_left {b : Matrix (Fin n) (Fin n) K} (hb : b.IsUpperTriangular)
    (hd : ∀ r, b r r ≠ 0) (M : Matrix (Fin n) (Fin n) K) (i j : ℕ) :
    cornerRank (b * M) i j = cornerRank M i j := by
  classical
  unfold cornerRank
  have hfac : (b * M).submatrix (fun r : {r : Fin n // i ≤ (r : ℕ) + 1} => (r : Fin n))
      (fun c : {c : Fin n // (c : ℕ) + 1 ≤ j} => (c : Fin n)) =
      b.submatrix (fun r : {r : Fin n // i ≤ (r : ℕ) + 1} => (r : Fin n))
          (fun r : {r : Fin n // i ≤ (r : ℕ) + 1} => (r : Fin n)) *
        M.submatrix (fun r : {r : Fin n // i ≤ (r : ℕ) + 1} => (r : Fin n))
          (fun c : {c : Fin n // (c : ℕ) + 1 ≤ j} => (c : Fin n)) := by
    ext r c
    simp only [submatrix_apply, mul_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun s : Fin n => i ≤ (s : ℕ) + 1)
      (fun s : Fin n => b (r : Fin n) s * M s (c : Fin n))]
    have hz : ∑ s : {s : Fin n // ¬ i ≤ (s : ℕ) + 1}, b (r : Fin n) s * M s (c : Fin n) = 0 :=
      Finset.sum_eq_zero fun s _ => by
        rw [hb (show (s : Fin n) < r by rw [Fin.lt_def]; have := s.2; have := r.2; omega),
          zero_mul]
    rw [hz, add_zero]
  rw [hfac, rank_mul_eq_right_of_isUnit_det _ _
    (isUnit_det_submatrix_of_isUpperTriangular hb hd _)]

theorem cornerRank_mul_right {b : Matrix (Fin n) (Fin n) K} (hb : b.IsUpperTriangular)
    (hd : ∀ r, b r r ≠ 0) (M : Matrix (Fin n) (Fin n) K) (i j : ℕ) :
    cornerRank (M * b) i j = cornerRank M i j := by
  classical
  unfold cornerRank
  have hfac : (M * b).submatrix (fun r : {r : Fin n // i ≤ (r : ℕ) + 1} => (r : Fin n))
      (fun c : {c : Fin n // (c : ℕ) + 1 ≤ j} => (c : Fin n)) =
      M.submatrix (fun r : {r : Fin n // i ≤ (r : ℕ) + 1} => (r : Fin n))
          (fun c : {c : Fin n // (c : ℕ) + 1 ≤ j} => (c : Fin n)) *
        b.submatrix (fun c : {c : Fin n // (c : ℕ) + 1 ≤ j} => (c : Fin n))
          (fun c : {c : Fin n // (c : ℕ) + 1 ≤ j} => (c : Fin n)) := by
    ext r c
    simp only [submatrix_apply, mul_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun s : Fin n => (s : ℕ) + 1 ≤ j)
      (fun s : Fin n => M (r : Fin n) s * b s (c : Fin n))]
    have hz : ∑ s : {s : Fin n // ¬ (s : ℕ) + 1 ≤ j}, M (r : Fin n) s * b s (c : Fin n) = 0 :=
      Finset.sum_eq_zero fun s _ => by
        rw [hb (show (c : Fin n) < s by rw [Fin.lt_def]; have := s.2; have := c.2; omega),
          mul_zero]
    rw [hz, add_zero]
  rw [hfac, rank_mul_eq_left_of_isUnit_det _ _
    (isUnit_det_submatrix_of_isUpperTriangular hb hd _)]

theorem cornerRank_permMatrix (w : Equiv.Perm (Fin n)) (i j : ℕ) :
    cornerRank (permMatrix n K w) i j = cornerCount w i j := by
  classical
  set R := {r : Fin n // i ≤ (r : ℕ) + 1}
  set C := {c : Fin n // (c : ℕ) + 1 ≤ j}
  set S := {r : R // ((w⁻¹ (r : Fin n) : Fin n) : ℕ) + 1 ≤ j}
  unfold cornerRank
  rw [rank_eq_finrank_span_cols]
  have hspan : Submodule.span K (Set.range ((permMatrix n K w).submatrix
      (fun r : R => (r : Fin n)) (fun c : C => (c : Fin n))).col) =
      Submodule.span K (Set.range fun r : S => (Pi.single r.1 (1 : K) : R → K)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      by_cases hc : i ≤ ((w c : Fin n) : ℕ) + 1
      · have hcol : ((permMatrix n K w).submatrix (fun r : R => (r : Fin n))
            (fun c : C => (c : Fin n))).col c = Pi.single ⟨w c, hc⟩ 1 := by
          ext r
          simp only [col_apply, submatrix_apply, permMatrix_apply, Pi.single_apply]
          by_cases h : (r : Fin n) = w c
          · rw [ite_eq_left h, ite_eq_left (Subtype.ext h)]
          · rw [ite_eq_right h, ite_eq_right (fun h' => h (congrArg Subtype.val h'))]
        rw [hcol]
        exact Submodule.subset_span ⟨⟨⟨w c, hc⟩, by simpa using c.2⟩, rfl⟩
      · have hcol : ((permMatrix n K w).submatrix (fun r : R => (r : Fin n))
            (fun c : C => (c : Fin n))).col c = 0 := by
          ext r
          simp only [col_apply, submatrix_apply, permMatrix_apply, Pi.zero_apply]
          rw [ite_eq_right_iff]
          intro h
          exact absurd (h ▸ r.2) hc
        rw [hcol]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      refine Submodule.subset_span ⟨⟨w⁻¹ (r.1 : Fin n), r.2⟩, ?_⟩
      ext s
      simp only [col_apply, submatrix_apply, permMatrix_apply, Pi.single_apply,
        Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
      by_cases h : (s : Fin n) = r.1
      · rw [ite_eq_left h, ite_eq_left (Subtype.ext h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (congrArg Subtype.val h'))]
  have hli : LinearIndependent K (fun r : S => (Pi.single r.1 (1 : K) : R → K)) :=
    (Pi.linearIndependent_single_one R K).comp _ Subtype.val_injective
  rw [hspan, finrank_span_eq_card hli, cornerCount, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun r => ⟨w⁻¹ r.1.1, r.2, by simpa using r.1.2⟩
      invFun := fun a => ⟨⟨w a.1, a.2.2⟩, by simpa using a.2.1⟩
      left_inv := fun r => by simp
      right_inv := fun a => by simp }

theorem cornerRank_signedPermMatrix (w : Equiv.Perm (Fin n)) (i j : ℕ) :
    cornerRank (signedPermMatrix n K w) i j = cornerCount w i j := by
  rw [signedPermMatrix, cornerRank_mul_left, cornerRank_permMatrix]
  · exact fun r s hrs => diagonal_apply_ne _ (ne_of_gt hrs)
  · intro r
    rw [diagonal_apply_eq]
    split_ifs
    · rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
    · exact one_ne_zero

theorem eq_of_cornerCount_eq {w w' : Equiv.Perm (Fin n)}
    (h : ∀ i j : ℕ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → cornerCount w i j = cornerCount w' i j) :
    w = w' := by
  classical
  have hstep : ∀ (v : Equiv.Perm (Fin n)) (i : ℕ) (c : Fin n),
      cornerCount v i ((c : ℕ) + 1) =
        cornerCount v i c + if i ≤ ((v c : Fin n) : ℕ) + 1 then 1 else 0 := by
    intro v i c
    have hunion : (Finset.univ.filter fun a : Fin n =>
        (a : ℕ) + 1 ≤ (c : ℕ) + 1 ∧ i ≤ ((v a : Fin n) : ℕ) + 1) =
        (Finset.univ.filter fun a : Fin n => (a : ℕ) + 1 ≤ c ∧ i ≤ ((v a : Fin n) : ℕ) + 1) ∪
          (Finset.univ.filter fun a : Fin n => a = c ∧ i ≤ ((v a : Fin n) : ℕ) + 1) := by
      ext a
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge (a : ℕ) c with h | h
        · exact Or.inl ⟨by omega, h2⟩
        · exact Or.inr ⟨Fin.ext (by omega), h2⟩
      · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
        · exact ⟨by omega, h2⟩
        · exact ⟨le_rfl, h2⟩
    have hdisj : Disjoint
        (Finset.univ.filter fun a : Fin n => (a : ℕ) + 1 ≤ c ∧ i ≤ ((v a : Fin n) : ℕ) + 1)
        (Finset.univ.filter fun a : Fin n => a = c ∧ i ≤ ((v a : Fin n) : ℕ) + 1) := by
      rw [Finset.disjoint_filter]
      rintro a - ⟨h1, -⟩ ⟨rfl, -⟩
      omega
    rw [cornerCount, cornerCount, hunion, Finset.card_union_of_disjoint hdisj]
    congr 1
    split_ifs with hi
    · rw [Finset.card_eq_one]
      refine ⟨c, ?_⟩
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h, -⟩
        exact h
      · rintro rfl
        exact ⟨rfl, hi⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro a - ⟨rfl, ha⟩
      exact hi ha
  have hzero : ∀ (v : Equiv.Perm (Fin n)) (i : ℕ), cornerCount v i 0 = 0 := fun v i => by
    rw [cornerCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a - ⟨h, -⟩
    omega
  have hcol : ∀ (c : Fin n) (i : ℕ), 1 ≤ i → i ≤ n →
      (i ≤ ((w c : Fin n) : ℕ) + 1 ↔ i ≤ ((w' c : Fin n) : ℕ) + 1) := by
    intro c i hi hin
    have h1 := h i ((c : ℕ) + 1) hi hin (by omega) (by omega)
    rw [hstep, hstep] at h1
    have h0 : cornerCount w i c = cornerCount w' i c := by
      rcases Nat.eq_zero_or_pos (c : ℕ) with hc | hc
      · rw [hc, hzero, hzero]
      · exact h i c hi hin hc (by omega)
    rw [h0] at h1
    constructor
    · intro hw
      by_contra hw'
      rw [ite_eq_left hw, ite_eq_right hw'] at h1
      omega
    · intro hw'
      by_contra hw
      rw [ite_eq_right hw, ite_eq_left hw'] at h1
      omega
  refine Equiv.ext fun c => Fin.ext ?_
  have h1 := (hcol c ((w c : ℕ) + 1) (by omega) (by omega)).mp le_rfl
  have h2 := (hcol c ((w' c : ℕ) + 1) (by omega) (by omega)).mpr le_rfl
  omega

theorem exists_mem_bruhatCell (g : SpecialLinearGroup (Fin n) K) :
    ∃ w : Equiv.Perm (Fin n), g ∈ bruhatCell w := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, mem_bruhatCell.mpr ⟨1, one_mem _, 1, one_mem _, Subsingleton.elim _ _⟩⟩
  obtain ⟨τ, hτ⟩ := TauCeti.exists_mem_doubleCoset_permutationGL (SpecialLinearGroup.toGL g)
  obtain ⟨L, hL, R, hR, hLR⟩ := DoubleCoset.mem_doubleCoset.mp hτ
  have hLtri : (L : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
    TauCeti.UpperTriangularGroup.mem_iff.mp hL
  have hRtri : (R : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
    TauCeti.UpperTriangularGroup.mem_iff.mp hR
  obtain ⟨D, hDtri, hD0, hP⟩ : ∃ D : Matrix (Fin n) (Fin n) K, D.IsUpperTriangular ∧
      D.det ≠ 0 ∧ permMatrix n K τ = D * signedPermMatrix n K τ := by
    set ε : Fin n → K := fun a => if (a : ℕ) = 0 then ((Equiv.Perm.sign τ : ℤ) : K) else 1
      with hε
    have hεε : ∀ a, ε a * ε a = 1 := fun a => by
      simp only [hε]
      split_ifs
      · rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      · exact mul_one 1
    refine ⟨diagonal ε, blockTriangular_diagonal _, ?_, ?_⟩
    · rw [det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun a _ h => by
        have := hεε a
        rw [h, zero_mul] at this
        exact zero_ne_one this
    · rw [signedPermMatrix, ← Matrix.mul_assoc, diagonal_mul_diagonal]
      convert (Matrix.one_mul (permMatrix n K τ)).symm
      rw [← diagonal_one]
      congr 1
      funext a
      exact hεε a
  have hg : (g : Matrix (Fin n) (Fin n) K) =
      (L : Matrix (Fin n) (Fin n) K) * D * signedPermMatrix n K τ *
        (R : Matrix (Fin n) (Fin n) K) := by
    have h := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hLR
    simp only [Units.val_mul, TauCeti.permutationGL_coe] at h
    change (g : Matrix (Fin n) (Fin n) K) = _ at h
    rw [h, ← permMatrix_eq, hP, Matrix.mul_assoc (L : Matrix (Fin n) (Fin n) K) D]
  have hMtri : ((L : Matrix (Fin n) (Fin n) K) * D).IsUpperTriangular := hLtri.mul hDtri
  have hd0 : ((L : Matrix (Fin n) (Fin n) K) * D).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero (L.isUnit.map Matrix.detMonoidHom).ne_zero hD0
  have hdet : ((L : Matrix (Fin n) (Fin n) K) * D).det * (R : Matrix (Fin n) (Fin n) K).det =
      1 := by
    have h1 := g.2
    rw [hg, det_mul, det_mul, det_signedPermMatrix, mul_one] at h1
    exact h1
  set d := ((L : Matrix (Fin n) (Fin n) K) * D).det with hd
  set t : Fin n → K := Pi.mulSingle ⟨0, hn⟩ d with ht
  have ht0 : ∀ a, t a ≠ 0 := fun a => by
    rw [ht, Pi.mulSingle_apply]
    split_ifs
    · exact hd0
    · exact one_ne_zero
  have hswap : diagonal t * signedPermMatrix n K τ =
      signedPermMatrix n K τ * diagonal (fun c => t (τ c)) := by
    ext r c
    rw [diagonal_mul, mul_diagonal, signedPermMatrix, diagonal_mul, permMatrix_apply]
    by_cases h : r = τ c
    · subst h
      ring
    · simp [h]
  have hinv : diagonal (fun a => (t a)⁻¹) * diagonal t = (1 : Matrix (Fin n) (Fin n) K) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (ht0 a)
  have hb₁det : ((L : Matrix (Fin n) (Fin n) K) * D * diagonal (fun a => (t a)⁻¹)).det = 1 := by
    rw [det_mul, det_diagonal, ← hd, Finset.prod_inv_distrib, ht, Fintype.prod_pi_mulSingle',
      mul_inv_cancel₀ hd0]
  have hb₂det : (diagonal (fun c => t (τ c)) * (R : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [det_mul, det_diagonal, Equiv.prod_comp τ t, ht, Fintype.prod_pi_mulSingle', hdet]
  refine ⟨τ, mem_bruhatCell.mpr ⟨⟨_, hb₁det⟩, ?_, ⟨_, hb₂det⟩, ?_, ?_⟩⟩
  · exact mem_upperTriangular_iff_isUpperTriangular.mpr (hMtri.mul (blockTriangular_diagonal _))
  · exact mem_upperTriangular_iff_isUpperTriangular.mpr ((blockTriangular_diagonal _).mul hRtri)
  · apply Subtype.ext
    change (g : Matrix (Fin n) (Fin n) K) =
      (L : Matrix (Fin n) (Fin n) K) * D * diagonal (fun a => (t a)⁻¹) *
        signedPermMatrix n K τ * (diagonal (fun c => t (τ c)) * (R : Matrix (Fin n) (Fin n) K))
    calc (g : Matrix (Fin n) (Fin n) K) =
        (L : Matrix (Fin n) (Fin n) K) * D * (diagonal (fun a => (t a)⁻¹) * diagonal t) *
          signedPermMatrix n K τ * (R : Matrix (Fin n) (Fin n) K) := by
          rw [hinv, Matrix.mul_one, hg]
      _ = (L : Matrix (Fin n) (Fin n) K) * D * diagonal (fun a => (t a)⁻¹) *
          (diagonal t * signedPermMatrix n K τ) * (R : Matrix (Fin n) (Fin n) K) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hswap]
          simp only [Matrix.mul_assoc]

theorem triangular_bruhat :
    (∀ g : SpecialLinearGroup (Fin n) K, ∃ w : Equiv.Perm (Fin n), g ∈ bruhatCell w) ∧
    (∀ (g : SpecialLinearGroup (Fin n) K) (w w' : Equiv.Perm (Fin n)),
      g ∈ bruhatCell w → g ∈ bruhatCell w' → w = w') ∧
    (∀ (g : SpecialLinearGroup (Fin n) K) (w : Equiv.Perm (Fin n)),
      g ∈ bruhatCell w ↔ ∀ i j : ℕ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
        cornerRank (g : Matrix (Fin n) (Fin n) K) i j = cornerCount w i j) := by
  have hrank : ∀ (g : SpecialLinearGroup (Fin n) K) (w : Equiv.Perm (Fin n)),
      g ∈ bruhatCell w → ∀ i j : ℕ,
        cornerRank (g : Matrix (Fin n) (Fin n) K) i j = cornerCount w i j := by
    intro g w hg i j
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.mp hg
    simp only [SpecialLinearGroup.coe_mul, coe_signedPermutation]
    rw [cornerRank_mul_right (mem_upperTriangular_iff_isUpperTriangular.mp hb₂)
        (upperTriangular_apply_self_ne_zero hb₂),
      cornerRank_mul_left (mem_upperTriangular_iff_isUpperTriangular.mp hb₁)
        (upperTriangular_apply_self_ne_zero hb₁), cornerRank_signedPermMatrix]
  have huniq : ∀ (g : SpecialLinearGroup (Fin n) K) (w w' : Equiv.Perm (Fin n)),
      g ∈ bruhatCell w → g ∈ bruhatCell w' → w = w' := fun g w w' hw hw' =>
    eq_of_cornerCount_eq fun i j _ _ _ _ => (hrank g w hw i j).symm.trans (hrank g w' hw' i j)
  refine ⟨exists_mem_bruhatCell, huniq, fun g w => ⟨fun hg i j _ _ _ _ => hrank g w hg i j,
    fun h => ?_⟩⟩
  obtain ⟨w', hw'⟩ := exists_mem_bruhatCell g
  rwa [eq_of_cornerCount_eq fun i j hi hin hj hjn =>
    (h i j hi hin hj hjn).symm.trans (hrank g w' hw' i j)]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
