module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type*} [Field K]

variable (K) in
@[expose] def compInd (J : Finset (Fin n)) : Matrix (Fin n) (Fin n) K :=
  diagonal fun i => if i ∈ J then 0 else 1

theorem compInd_mul_apply (J : Finset (Fin n)) (g : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (compInd K J * g) i j = if i ∈ J then 0 else g i j := by
  rw [compInd, diagonal_mul]
  split_ifs <;> simp

theorem mul_compInd_apply (J : Finset (Fin n)) (g : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (g * compInd K J) i j = if j ∈ J then 0 else g i j := by
  rw [compInd, mul_diagonal]
  split_ifs <;> simp

theorem compInd_apply (J : Finset (Fin n)) (i j : Fin n) :
    compInd K J i j = if i ∉ J ∧ i = j then 1 else 0 := by
  rw [compInd, diagonal_apply]
  by_cases hij : i = j <;> by_cases hi : i ∈ J <;> simp [hij, hi]

theorem commute_compInd_iff (J : Finset (Fin n)) (D : Matrix (Fin n) (Fin n) K) :
    compInd K J * D = D * compInd K J ↔ ∀ i j, (i ∈ J ↔ j ∉ J) → D i j = 0 := by
  constructor
  · intro h i j hij
    have := congrFun (congrFun h i) j
    rw [compInd_mul_apply, mul_compInd_apply] at this
    by_cases hi : i ∈ J
    · have hj : j ∉ J := hij.1 hi
      simp only [hi, hj, ite_true, ite_false] at this
      exact this.symm
    · have hj : j ∈ J := by
        by_contra hj
        exact hi (hij.2 hj)
      simp only [hi, hj, ite_true, ite_false] at this
      exact this
  · intro h
    ext i j
    rw [compInd_mul_apply, mul_compInd_apply]
    by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
    · simp only [hi, hj, ite_true]
    · simp only [hi, hj, ite_true, ite_false]
      exact (h i j (iff_of_true hi hj)).symm
    · simp only [hi, hj, ite_true, ite_false]
      exact h i j (iff_of_false hi (not_not.2 hj))
    · simp only [hi, hj, ite_false]

variable (K) in
@[expose] def coordBlock (J : Finset (Fin n)) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | compInd K J * (g : Matrix (Fin n) (Fin n) K) = compInd K J ∧
    (g : Matrix (Fin n) (Fin n) K) * compInd K J = compInd K J}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    change compInd K J * ((g : Matrix (Fin n) (Fin n) K) * h) = compInd K J ∧
      ((g : Matrix (Fin n) (Fin n) K) * h) * compInd K J = compInd K J
    exact ⟨by rw [← Matrix.mul_assoc, hg1, hh1], by rw [Matrix.mul_assoc, hh2, hg2]⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    set gi : Matrix (Fin n) (Fin n) K :=
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) with hgi
    have h1 : (g : Matrix (Fin n) (Fin n) K) * gi = 1 := by
      rw [hgi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h2 : gi * (g : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hgi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    change compInd K J * gi = compInd K J ∧ gi * compInd K J = compInd K J
    refine ⟨?_, ?_⟩
    · calc compInd K J * gi = (compInd K J * g) * gi := by rw [hg1]
        _ = compInd K J := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    · calc gi * compInd K J = gi * (g * compInd K J) := by rw [hg2]
        _ = compInd K J := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem mem_coordBlock_iff {J : Finset (Fin n)} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ coordBlock K J ↔ ∀ i j, (i ∉ J ∨ j ∉ J) →
      (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have := congrFun (congrFun h1 i) j
      simp only [compInd_mul_apply, compInd_apply, hi, not_false_eq_true, true_and,
        ite_false] at this
      rw [this]
    · have := congrFun (congrFun h2 i) j
      simp only [mul_compInd_apply, compInd_apply, hj, ite_false] at this
      rw [this]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [hij]
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j
      rw [compInd_mul_apply, compInd_apply]
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ite_false, not_false_eq_true, true_and]
        exact h i j (Or.inl hi)
    · ext i j
      rw [mul_compInd_apply, compInd_apply]
      by_cases hj : j ∈ J
      · by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hj, hij]
      · simp only [hj, ite_false]
        rw [h i j (Or.inr hj)]
        by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hij]

theorem conj_mem_coordBlock {J : Finset (Fin n)} {D Di : Matrix (Fin n) (Fin n) K}
    (hDD : D * Di = 1) (hDiD : Di * D = 1) (hD : compInd K J * D = D * compInd K J)
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ coordBlock K J)
    {h : SpecialLinearGroup (Fin n) K} (hh : (h : Matrix (Fin n) (Fin n) K) = D * g * Di) :
    h ∈ coordBlock K J := by
  obtain ⟨hg1, hg2⟩ := hg
  set P := compInd K J with hP
  have hDiP : P * Di = Di * P := by
    calc P * Di = Di * D * P * Di := by rw [hDiD, Matrix.one_mul]
      _ = Di * (D * P) * Di := by simp only [Matrix.mul_assoc]
      _ = Di * (P * D) * Di := by rw [hD]
      _ = Di * P * (D * Di) := by simp only [Matrix.mul_assoc]
      _ = Di * P := by rw [hDD, Matrix.mul_one]
  change P * (h : Matrix (Fin n) (Fin n) K) = P ∧ (h : Matrix (Fin n) (Fin n) K) * P = P
  rw [hh]
  refine ⟨?_, ?_⟩
  · calc P * (D * g * Di) = D * (P * g) * Di := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hD]; simp only [Matrix.mul_assoc]
      _ = D * (P * Di) := by rw [hg1, Matrix.mul_assoc]
      _ = D * (Di * P) := by rw [hDiP]
      _ = P := by rw [← Matrix.mul_assoc, hDD, Matrix.one_mul]
  · calc (D * g * Di) * P = D * (g * P) * Di := by
          rw [Matrix.mul_assoc, ← hDiP]; simp only [Matrix.mul_assoc]
      _ = (D * P) * Di := by rw [hg2]
      _ = (P * D) * Di := by rw [hD]
      _ = P := by rw [Matrix.mul_assoc, hDD, Matrix.mul_one]

variable (K) in
@[expose] def blockOn (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) K) :
    Matrix (Fin n) (Fin n) K :=
  reindexAlgEquiv K K (Equiv.sumCompl (· ∈ J))
    (fromBlocks (reindexAlgEquiv K K J.equivFin.symm X) 0 0 1)

theorem blockOn_one (J : Finset (Fin n)) : blockOn K J 1 = 1 := by
  rw [blockOn, map_one, fromBlocks_one, map_one]

theorem blockOn_mul (J : Finset (Fin n)) (X Y : Matrix (Fin J.card) (Fin J.card) K) :
    blockOn K J (X * Y) = blockOn K J X * blockOn K J Y := by
  rw [blockOn, blockOn, blockOn, ← map_mul, fromBlocks_multiply, map_mul]
  simp

theorem det_blockOn (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) K) :
    (blockOn K J X).det = X.det := by
  rw [blockOn, coe_reindexAlgEquiv, det_reindex_self, det_fromBlocks_zero₂₁, coe_reindexAlgEquiv,
    det_reindex_self, det_one, mul_one]

theorem blockOn_apply_mem (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) K)
    {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J) :
    blockOn K J X i j = X (J.equivFin ⟨i, hi⟩) (J.equivFin ⟨j, hj⟩) := by
  rw [blockOn, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
    Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_pos hj, fromBlocks_apply₁₁,
    coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  rfl

theorem blockOn_apply_not_mem (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) K)
    {i j : Fin n} (hij : i ∉ J ∨ j ∉ J) : blockOn K J X i j = if i = j then 1 else 0 := by
  rw [blockOn, coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · exact absurd (hij.elim (fun h => absurd hi h) fun h => absurd hj h) id
  · rw [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₁₂, Matrix.zero_apply]
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [hne]
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_pos hj,
      fromBlocks_apply₂₁, Matrix.zero_apply]
    have hne : i ≠ j := fun h => hi (h ▸ hj)
    simp [hne]
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₂₂, one_apply]
    by_cases h : i = j
    · subst h
      simp
    · have h' : (⟨i, hi⟩ : {a // a ∉ J}) ≠ ⟨j, hj⟩ := fun h' => h (congrArg Subtype.val h')
      simp only [h, h', ite_false]

variable (K) in
@[expose] def blockSL (J : Finset (Fin n)) :
    SpecialLinearGroup (Fin J.card) K →* SpecialLinearGroup (Fin n) K where
  toFun X := ⟨blockOn K J X, (det_blockOn J (X : Matrix (Fin J.card) (Fin J.card) K)).trans X.2⟩
  map_one' := Subtype.ext <| by
    show blockOn K J ((1 : SpecialLinearGroup (Fin J.card) K) : Matrix _ _ K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact blockOn_one J
  map_mul' X Y := Subtype.ext <| by
    show blockOn K J ((X * Y : SpecialLinearGroup (Fin J.card) K) : Matrix _ _ K) =
      blockOn K J X * blockOn K J Y
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact blockOn_mul J _ _

theorem coe_blockSL (J : Finset (Fin n)) (X : SpecialLinearGroup (Fin J.card) K) :
    (blockSL K J X : Matrix (Fin n) (Fin n) K) = blockOn K J X :=
  rfl

theorem blockSL_injective (J : Finset (Fin n)) : Function.Injective (blockSL K J) := by
  intro X Y h
  ext a b
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K) (J.equivFin.symm a) (J.equivFin.symm b)) h
  simp only [coe_blockSL] at h1
  rw [blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
    blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at h1
  simpa using h1

theorem range_blockSL (J : Finset (Fin n)) : (blockSL K J).range = coordBlock K J := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [mem_coordBlock_iff]
    intro i j hij
    rw [coe_blockSL, blockOn_apply_not_mem J _ hij]
  · intro g hg
    rw [mem_coordBlock_iff] at hg
    set X : Matrix (Fin J.card) (Fin J.card) K :=
      Matrix.of fun a b => (g : Matrix (Fin n) (Fin n) K) (J.equivFin.symm a) (J.equivFin.symm b)
      with hX
    have hXg : blockOn K J X = (g : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · rw [blockOn_apply_mem J X hi hj, hX, of_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      · rw [blockOn_apply_not_mem J X (Or.inr hj), hg i j (Or.inr hj)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
    have hdet : X.det = 1 := by
      rw [← det_blockOn J X, hXg]
      exact g.2
    exact ⟨⟨X, hdet⟩, Subtype.ext hXg⟩

@[expose] def coordBlockEquiv (J : Finset (Fin n)) :
    SpecialLinearGroup (Fin J.card) K ≃* coordBlock K J :=
  (MonoidHom.ofInjective (blockSL_injective (K := K) J)).trans
    (MulEquiv.subgroupCongr (range_blockSL J))

theorem coe_coordBlockEquiv (J : Finset (Fin n)) (X : SpecialLinearGroup (Fin J.card) K) :
    ((coordBlockEquiv J X : coordBlock K J) : SpecialLinearGroup (Fin n) K) = blockSL K J X :=
  rfl

theorem isQuasisimple_coordBlock [Finite K] {J : Finset (Fin n)} (hJ : 2 ≤ J.card)
    (hq : 3 ≤ J.card ∨ 4 ≤ Nat.card K) : IsQuasisimple (coordBlock K J) := by
  refine LocalCores.isQuasisimple_of_mulEquiv (coordBlockEquiv J)
    (CatalogueBGeneralLinear.specialLinear_quasisimple J.card K hJ ?_ ?_)
  · rcases hq with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hq with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end CFSG.ComponentClassification.Burgoyne.PSL
