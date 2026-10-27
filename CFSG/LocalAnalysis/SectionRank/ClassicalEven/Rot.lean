module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic

public section

namespace CFSG.SectionRank.ClassicalEven

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

section Rotation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]

@[expose] def rotCol (i j b : ι) : ι → K :=
  if b = i then Pi.single j 1 else if b = j then -Pi.single i 1 - Pi.single j 1 else Pi.single b 1

@[expose] def rotMatrix (i j : ι) : Matrix ι ι K :=
  Matrix.of fun a b => rotCol i j b a

theorem rotMatrix_mulVec_single (i j b : ι) :
    rotMatrix (K := K) i j *ᵥ Pi.single b 1 = rotCol i j b := by
  rw [mulVec_single_one]
  rfl

theorem rotMatrix_mulVec_left (i j : ι) :
    rotMatrix (K := K) i j *ᵥ Pi.single i 1 = Pi.single j 1 := by
  rw [rotMatrix_mulVec_single, rotCol, ite_eq_left rfl]

theorem rotMatrix_mulVec_right {i j : ι} (h : i ≠ j) :
    rotMatrix (K := K) i j *ᵥ Pi.single j 1 = -Pi.single i 1 - Pi.single j 1 := by
  rw [rotMatrix_mulVec_single, rotCol, ite_eq_right h.symm, ite_eq_left rfl]

theorem rotMatrix_mulVec_of_ne {i j b : ι} (hi : b ≠ i) (hj : b ≠ j) :
    rotMatrix (K := K) i j *ᵥ Pi.single b 1 = Pi.single b 1 := by
  rw [rotMatrix_mulVec_single, rotCol, ite_eq_right hi, ite_eq_right hj]

theorem rotMatrix_transpose_mulVec_left {i j : ι} (h : i ≠ j) :
    (rotMatrix (K := K) i j)ᵀ *ᵥ Pi.single i 1 = -Pi.single j 1 := by
  rw [mulVec_single_one, col_transpose]
  ext a
  simp only [row, rotMatrix, of_apply, rotCol]
  split_ifs <;> simp_all

theorem rotMatrix_transpose_mulVec_right {i j : ι} (h : i ≠ j) :
    (rotMatrix (K := K) i j)ᵀ *ᵥ Pi.single j 1 = Pi.single i 1 - Pi.single j 1 := by
  rw [mulVec_single_one, col_transpose]
  ext a
  simp only [row, rotMatrix, of_apply, rotCol]
  split_ifs <;> simp_all

theorem rotMatrix_transpose_mulVec_of_ne {i j b : ι} (hi : b ≠ i) (hj : b ≠ j) :
    (rotMatrix (K := K) i j)ᵀ *ᵥ Pi.single b 1 = Pi.single b 1 := by
  rw [mulVec_single_one, col_transpose]
  ext a
  simp only [row, rotMatrix, of_apply, rotCol]
  split_ifs <;> simp_all [Pi.single_apply, eq_comm]

theorem rotMatrix_self (i : ι) : rotMatrix (K := K) i i = 1 := by
  refine ext_of_mulVec_single fun b => ?_
  rw [one_mulVec]
  by_cases hb : b = i
  · rw [hb, rotMatrix_mulVec_left]
  · exact rotMatrix_mulVec_of_ne hb hb

theorem rotMatrix_pow_three (i j : ι) : rotMatrix (K := K) i j ^ 3 = 1 := by
  by_cases hij : i = j
  · rw [hij, rotMatrix_self, one_pow]
  refine ext_of_mulVec_single fun b => ?_
  rw [pow_three, ← mulVec_mulVec, ← mulVec_mulVec, one_mulVec]
  by_cases hbi : b = i
  · rw [hbi]
    simp only [rotMatrix_mulVec_left, rotMatrix_mulVec_right hij, mulVec_sub, mulVec_neg]
    abel
  by_cases hbj : b = j
  · rw [hbj]
    simp only [rotMatrix_mulVec_left, rotMatrix_mulVec_right hij, mulVec_sub, mulVec_neg]
    abel
  · rw [rotMatrix_mulVec_of_ne hbi hbj, rotMatrix_mulVec_of_ne hbi hbj,
      rotMatrix_mulVec_of_ne hbi hbj]

theorem rotMatrix_commute {i j k l : ι} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Commute (rotMatrix (K := K) i j) (rotMatrix k l) := by
  by_cases hij : i = j
  · rw [hij, rotMatrix_self]
    exact Commute.one_left _
  by_cases hkl : k = l
  · rw [hkl, rotMatrix_self]
    exact Commute.one_right _
  refine ext_of_mulVec_single fun b => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  by_cases hbi : b = i
  · rw [hbi, rotMatrix_mulVec_of_ne hik hil, rotMatrix_mulVec_left, rotMatrix_mulVec_of_ne hjk hjl]
  by_cases hbj : b = j
  · rw [hbj, rotMatrix_mulVec_of_ne hjk hjl, rotMatrix_mulVec_right hij, mulVec_sub, mulVec_neg,
      rotMatrix_mulVec_of_ne hik hil, rotMatrix_mulVec_of_ne hjk hjl]
  by_cases hbk : b = k
  · rw [hbk, rotMatrix_mulVec_of_ne hik.symm hjk.symm, rotMatrix_mulVec_left,
      rotMatrix_mulVec_of_ne hil.symm hjl.symm]
  by_cases hbl : b = l
  · rw [hbl, rotMatrix_mulVec_of_ne hil.symm hjl.symm, rotMatrix_mulVec_right hkl, mulVec_sub,
      mulVec_neg, rotMatrix_mulVec_of_ne hik.symm hjk.symm,
      rotMatrix_mulVec_of_ne hil.symm hjl.symm]
  · rw [rotMatrix_mulVec_of_ne hbk hbl, rotMatrix_mulVec_of_ne hbi hbj,
      rotMatrix_mulVec_of_ne hbk hbl]

theorem det_eq_of_eq_one_off_pair {i j : ι} (hij : i ≠ j) {M : Matrix ι ι K}
    (hM : ∀ a, a ≠ i → a ≠ j → ∀ b, M a b = (1 : Matrix ι ι K) a b) :
    M.det = M i i * M j j - M i j * M j i := by
  obtain ⟨p, rfl, rfl⟩ : ∃ p : Fin 2 → ι, p 0 = i ∧ p 1 = j := ⟨![i, j], rfl, rfl⟩
  let A : Matrix ι (Fin 2) K := Matrix.of fun a k => if a = p k then 1 else 0
  let B : Matrix (Fin 2) ι K := Matrix.of fun k b => (M - 1) (p k) b
  have hAB : M = 1 + A * B := by
    ext a b
    simp only [A, B, Matrix.add_apply, mul_apply, of_apply, Fin.sum_univ_two, Matrix.sub_apply]
    by_cases ha0 : a = p 0
    · rw [ha0, ite_eq_left rfl, ite_eq_right hij]
      ring
    by_cases ha1 : a = p 1
    · rw [ha1, ite_eq_left rfl, ite_eq_right hij.symm]
      ring
    · rw [ite_eq_right ha0, ite_eq_right ha1, hM a ha0 ha1 b]
      ring
  have hBA : 1 + B * A = !![M (p 0) (p 0), M (p 0) (p 1); M (p 1) (p 0), M (p 1) (p 1)] := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [A, B, mul_apply, one_apply, hij, hij.symm, mul_ite, Finset.sum_ite_eq']
  rw [congrArg det hAB, det_one_add_mul_comm, hBA, det_fin_two_of]

theorem det_rotMatrix (i j : ι) : (rotMatrix (K := K) i j).det = 1 := by
  by_cases hij : i = j
  · rw [hij, rotMatrix_self, det_one]
  rw [det_eq_of_eq_one_off_pair hij]
  · simp [rotMatrix, rotCol, hij, Ne.symm hij]
  · intro a hai haj b
    simp only [rotMatrix, rotCol, of_apply, one_apply]
    split_ifs <;> simp_all

@[expose] def rotGL (i j : ι) : GL ι K :=
  ⟨rotMatrix i j, rotMatrix i j ^ 2, (pow_succ' _ 2).symm.trans (rotMatrix_pow_three i j),
    (pow_succ _ 2).symm.trans (rotMatrix_pow_three i j)⟩

theorem coe_rotGL (i j : ι) : (rotGL (K := K) i j : Matrix ι ι K) = rotMatrix i j :=
  rfl

theorem rotGL_pow_three (i j : ι) : rotGL (K := K) i j ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, coe_rotGL, rotMatrix_pow_three, Units.val_one])

theorem rotGL_commute {i j k l : ι} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Commute (rotGL (K := K) i j) (rotGL k l) :=
  Commute.units_val_iff.1 (rotMatrix_commute hik hil hjk hjl)

theorem rotGL_pow_mulVec_of_ne {i j b : ι} (hi : b ≠ i) (hj : b ≠ j) (n : ℕ) :
    ((rotGL (K := K) i j ^ n : GL ι K) : Matrix ι ι K) *ᵥ Pi.single b 1 = Pi.single b 1 := by
  rw [Units.val_pow_eq_pow_val, coe_rotGL]
  induction n with
  | zero => rw [pow_zero, one_mulVec]
  | succ n ih => rw [pow_succ, ← mulVec_mulVec, rotMatrix_mulVec_of_ne hi hj, ih]

end Rotation

theorem mul_scalar_ne {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {g h c : GL ι K}
    {a b : ι} (hab : a ≠ b) (hg : (g : Matrix ι ι K) *ᵥ Pi.single a 1 = Pi.single a 1)
    (hh : (h : Matrix ι ι K) *ᵥ Pi.single a 1 = Pi.single b 1) (hc : c ∈ StatedScalars ι K) :
    g * c ≠ h := by
  obtain ⟨u, rfl⟩ := hc
  intro he
  have := congrFun (congrArg (fun k : GL ι K => (k : Matrix ι ι K) *ᵥ Pi.single a 1) he) b
  simp only [Units.val_mul, ← mulVec_mulVec, GeneralLinearGroup.coe_scalar, scalar_apply,
    ← smul_one_eq_diagonal, smul_mulVec, one_mulVec, mulVec_smul, hg, hh] at this
  simp [hab] at this

theorem three_le_pRank_three_of_rotGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {e : Fin 3 ⊕ Fin 3 → ι} (he : Function.Injective e)
    (hH : ∀ k, rotGL (e (.inl k)) (e (.inr k)) ∈ H) :
    3 ≤ pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have hne : ∀ a b : Fin 3 ⊕ Fin 3, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  refine three_le_pRank_statedProj (hH 0) (hH 1) (hH 2) (rotGL_pow_three _ _)
    (rotGL_pow_three _ _) (rotGL_pow_three _ _)
    (rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (fun hx => mul_scalar_ne (g := 1) (hne _ _ (by decide)) (one_mulVec _)
      (rotMatrix_mulVec_left _ _) hx (one_mul _))
    (fun n _ hc => mul_scalar_ne (hne _ _ (by decide))
      (rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n)
      (rotMatrix_mulVec_left _ _) hc)
    (fun n m _ hc => mul_scalar_ne (hne _ _ (by decide)) ?_ (rotMatrix_mulVec_left _ _) hc)
  rw [Units.val_mul, ← mulVec_mulVec,
    rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m,
    rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n]

end CFSG.SectionRank.ClassicalEven
