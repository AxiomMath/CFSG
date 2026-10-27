module

public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

theorem conjTr_apply (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    conjTr σ A i j = σ (A j i) := by
  simp [conjTr]

theorem conjTr_zero : conjTr σ (0 : Matrix (Fin n) (Fin n) F) = 0 := by
  simp [conjTr]

theorem conjTr_smul (c : F) (A : Matrix (Fin n) (Fin n) F) :
    conjTr σ (c • A) = σ c • conjTr σ A := by
  ext i j
  simp [conjTr]

variable {σ}

theorem conjTr_conjTr (hσ : ∀ c, σ (σ c) = c) (A : Matrix (Fin n) (Fin n) F) :
    conjTr σ (conjTr σ A) = A := by
  ext i j
  simp [conjTr, hσ]

theorem conjTr_vecMulVec (hσ : ∀ c, σ (σ c) = c) (u w : Fin n → F) :
    conjTr σ (vecMulVec u (fun i => σ (w i))) = vecMulVec w (fun i => σ (u i)) := by
  ext i j
  simp [conjTr, vecMulVec, hσ, mul_comm]

private abbrev basisVec (i : Fin n) : Fin n → F := Pi.single i (1 : F)

private theorem map_basisVec (i : Fin n) :
    (fun k => σ (basisVec (F := F) i k)) = basisVec (F := F) i := by
  funext k
  by_cases h : k = i <;> simp [basisVec, Pi.single_apply, h]

private theorem vecMulVec_basisVec (i j : Fin n) :
    vecMulVec (basisVec (F := F) i) (basisVec (F := F) j) = single i j 1 := by
  simp only [basisVec]
  exact (Matrix.single_eq_single_vecMulVec_single i j).symm

private theorem sum_single_self_apply (B : Matrix (Fin n) (Fin n) F) (a b : Fin n) :
    (∑ i, single i i (B i i)) a b = if a = b then B a a else 0 := by
  rw [Matrix.sum_apply]
  have hsum : (∑ i, single i i (B i i) a b) = single a a (B a a) a b := by
    apply Finset.sum_eq_single a
    · intro i _ hia
      simp [Matrix.single_apply, hia]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [hsum]
  by_cases hab : a = b <;> simp [Matrix.single_apply, hab]

private theorem sum_single_offdiag_apply (B : Matrix (Fin n) (Fin n) F) (a b : Fin n) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (single p.1 p.2 (B p.1 p.2) + single p.2 p.1 (σ (B p.1 p.2)))) a b =
      if a < b then B a b else if b < a then σ (B b a) else 0 := by
  rw [Matrix.sum_apply]
  rcases lt_trichotomy a b with hab | heq | hba
  · rw [if_pos hab]
    have hsum : (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (single p.1 p.2 (B p.1 p.2) + single p.2 p.1 (σ (B p.1 p.2))) a b) =
        (single a b (B a b) + single b a (σ (B a b))) a b := by
      apply Finset.sum_eq_single (a, b)
      · intro p hp hne
        rw [Finset.mem_filter] at hp
        have h1 : ¬ (p.1 = a ∧ p.2 = b) := fun h => hne (Prod.ext h.1 h.2)
        have h2 : ¬ (p.2 = a ∧ p.1 = b) := by
          rintro ⟨h2a, h2b⟩
          exact (lt_asymm hab) (by simpa [h2a, h2b] using hp.2)
        simp [Matrix.add_apply, Matrix.single_apply, h1, h2]
      · intro hmem
        exfalso
        exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
    rw [hsum]
    simp [Matrix.add_apply, Matrix.single_apply, ne_of_lt hab]
  · subst b
    rw [if_neg (lt_irrefl a), if_neg (lt_irrefl a)]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    have hne : p.1 ≠ p.2 := ne_of_lt hp.2
    have h1 : ¬ (p.1 = a ∧ p.2 = a) := fun h => hne (h.1.trans h.2.symm)
    have h2 : ¬ (p.2 = a ∧ p.1 = a) := fun h => hne (h.2.trans h.1.symm)
    simp [Matrix.add_apply, Matrix.single_apply, h1, h2]
  · rw [if_neg (not_lt.mpr (le_of_lt hba)), if_pos hba]
    have hsum : (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (single p.1 p.2 (B p.1 p.2) + single p.2 p.1 (σ (B p.1 p.2))) a b) =
        (single b a (B b a) + single a b (σ (B b a))) a b := by
      apply Finset.sum_eq_single (b, a)
      · intro p hp hne
        rw [Finset.mem_filter] at hp
        have h1 : ¬ (p.1 = a ∧ p.2 = b) := by
          rintro ⟨h1a, h1b⟩
          exact (lt_asymm hba) (by simpa [h1a, h1b] using hp.2)
        have h2 : ¬ (p.2 = a ∧ p.1 = b) := fun h => hne (Prod.ext h.2 h.1)
        simp [Matrix.add_apply, Matrix.single_apply, h1, h2]
      · intro hmem
        exfalso
        exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba⟩)
    rw [hsum]
    simp [Matrix.add_apply, Matrix.single_apply, ne_of_lt hba]

private theorem eq_sum_of_add_conjTr_eq_zero [CharP F 2]
    {B : Matrix (Fin n) (Fin n) F} (hB : B + conjTr σ B = 0) :
    B = (∑ i, single i i (B i i)) +
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (single p.1 p.2 (B p.1 p.2) + single p.2 p.1 (σ (B p.1 p.2))) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single B]
  ext a b
  have hsum : (∑ i, ∑ j, single i j (B i j)) a b = B a b :=
    congrFun (congrFun (Matrix.sum_sum_single (fun i j => B i j)) a) b
  rw [hsum, Matrix.add_apply, sum_single_self_apply, sum_single_offdiag_apply]
  rcases lt_trichotomy a b with hab | heq | hba
  · rw [if_neg (ne_of_lt hab), if_pos hab, zero_add]
  · subst b
    simp
  · rw [if_neg (not_lt.mpr (le_of_lt hba)), if_pos hba, if_neg (ne_of_gt hba), zero_add]
    have h := congrFun (congrFun hB a) b
    rw [Matrix.add_apply, conjTr_apply] at h
    exact CharTwo.add_eq_zero.mp h

private theorem single_add_single_eq [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {i j : Fin n} (c : F) :
    single i j c + single j i (σ c) =
      vecMulVec (basisVec (F := F) i + σ c • basisVec (F := F) j : Fin n → F)
          (fun k => σ ((basisVec (F := F) i + σ c • basisVec (F := F) j :
            Fin n → F) k)) +
        vecMulVec (basisVec (F := F) i) (fun k => σ (basisVec (F := F) i k)) +
          (c * σ c) • vecMulVec (basisVec (F := F) j)
            (fun k => σ (basisVec (F := F) j k)) := by
  set u : Fin n → F := (basisVec (F := F) i + σ c • basisVec (F := F) j : Fin n → F)
    with hu
  have hsig : (fun k => σ (u k)) = basisVec (F := F) i + c • basisVec (F := F) j := by
    funext k
    simp only [u, Pi.add_apply, Pi.smul_apply, map_add, map_mul, basisVec, Pi.single_apply]
    by_cases hk : k = j
    · simp [hk, hσ]
    · simp [hk]
  have hvec : vecMulVec u (fun k => σ (u k)) =
      vecMulVec (basisVec (F := F) i) (basisVec (F := F) i) +
        c • vecMulVec (basisVec (F := F) i) (basisVec (F := F) j) +
          σ c • vecMulVec (basisVec (F := F) j) (basisVec (F := F) i) +
            (c * σ c) • vecMulVec (basisVec (F := F) j) (basisVec (F := F) j) := by
    rw [hsig, hu]
    simp only [add_vecMulVec, smul_vecMulVec, vecMulVec_add, vecMulVec_smul, smul_add,
      smul_smul]
    abel
  rw [hvec, map_basisVec, map_basisVec, vecMulVec_basisVec, vecMulVec_basisVec,
    vecMulVec_basisVec, vecMulVec_basisVec]
  simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  have hE : (single i i 1 : Matrix (Fin n) (Fin n) F) + single i i 1 = 0 := by
    ext a b
    simp [Matrix.add_apply, Matrix.single_apply, CharTwo.add_self_eq_zero]
  have hN : single j j (c * σ c) + single j j (c * σ c) = 0 := by
    ext a b
    simp [Matrix.add_apply, Matrix.single_apply, CharTwo.add_self_eq_zero]
  rw [show single i i 1 + single i j c + single j i (σ c) + single j j (c * σ c) +
        single i i 1 + single j j (c * σ c) =
      (single i j c + single j i (σ c)) + (single i i 1 + single i i 1) +
        (single j j (c * σ c) + single j j (c * σ c)) by abel]
  rw [hE, hN, add_zero, add_zero]

theorem mem_closure_smul_vecMulVec [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {B : Matrix (Fin n) (Fin n) F} (hB : B + conjTr σ B = 0) :
    B ∈ AddSubmonoid.closure {M | ∃ (c : F) (u : Fin n → F), σ c = c ∧
      M = c • vecMulVec u (fun i => σ (u i))} := by
  rw [eq_sum_of_add_conjTr_eq_zero hB]
  apply AddSubmonoid.add_mem
  · apply AddSubmonoid.sum_mem
    intro i _
    have hi : σ (B i i) = B i i := by
      have h := congrFun (congrFun hB i) i
      rw [Matrix.add_apply, conjTr_apply] at h
      exact (CharTwo.add_eq_zero.mp h).symm
    refine AddSubmonoid.subset_closure ⟨B i i, basisVec (F := F) i, hi, ?_⟩
    rw [map_basisVec, vecMulVec_basisVec, Matrix.smul_single]
    simp
  · apply AddSubmonoid.sum_mem
    intro p _
    obtain ⟨i, j⟩ := p
    have hfix : σ (B i j * σ (B i j)) = B i j * σ (B i j) := by
      rw [map_mul, hσ]
      ring
    rw [single_add_single_eq hσ]
    refine AddSubmonoid.add_mem _ (AddSubmonoid.add_mem _ ?_ ?_) ?_
    · exact AddSubmonoid.subset_closure
        ⟨1, basisVec (F := F) i + σ (B i j) • basisVec (F := F) j, by simp, by simp⟩
    · exact AddSubmonoid.subset_closure ⟨1, basisVec (F := F) i, by simp, by simp⟩
    · exact AddSubmonoid.subset_closure
        ⟨B i j * σ (B i j), basisVec (F := F) j, hfix, by simp⟩

end CFSG.LieType.Universal.Unitary
