module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussBlocks

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan

section Algebra

variable {F : Type} [Field F] [Fact (¬ IsSquare (-1 : F))]

@[expose] def dMat : Matrix (Fin 2) (Fin 2) (GaussField F) :=
  !![QuadraticAlgebra.omega, 0; 0, -QuadraticAlgebra.omega]

@[expose] def wMat : Matrix (Fin 2) (Fin 2) (GaussField F) := !![0, -1; 1, 0]

omit [Fact (¬ IsSquare (-1 : F))] in
theorem omega_mul_omega :
    (QuadraticAlgebra.omega : GaussField F) * QuadraticAlgebra.omega = -1 := by
  apply QuadraticAlgebra.ext <;>
    simp [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one]

omit [Fact (¬ IsSquare (-1 : F))] in
theorem det_dMat : (dMat (F := F)).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [dMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, sub_zero]
  exact omega_mul_neg_omega

omit [Fact (¬ IsSquare (-1 : F))] in
theorem det_wMat : (wMat (F := F)).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [wMat]

theorem omega_ne_one_aux (h2 : (2 : GaussField F) ≠ 0) :
    (QuadraticAlgebra.omega : GaussField F) ≠ 1 ∧ (QuadraticAlgebra.omega : GaussField F) ≠ -1 ∧
      (QuadraticAlgebra.omega : GaussField F) ≠ -QuadraticAlgebra.omega := by
  have hω := omega_mul_omega (F := F)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, mul_one] at hω
    exact h2 (by linear_combination hω)
  · rw [h, neg_mul_neg, mul_one] at hω
    exact h2 (by linear_combination hω)
  · have h0 : QuadraticAlgebra.omega = (0 : GaussField F) := by
      have : (2 : GaussField F) * QuadraticAlgebra.omega = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left h2
    rw [h0, mul_zero] at hω
    exact absurd hω (by
      intro h'
      have := congrArg QuadraticAlgebra.re h'
      simp [QuadraticAlgebra.re_one] at this)

@[expose] def dVec (m a : ℕ) : Fin m → GaussField F := fun r =>
  if r.val = a then QuadraticAlgebra.omega else if r.val = a + 1 then -QuadraticAlgebra.omega else 1

theorem blockMat_dMat (m a : ℕ) :
    blockMat m a (dMat (F := F)) = Matrix.diagonal (dVec m a) := by
  refine Matrix.ext fun r s => ?_
  rw [blockMat_apply]
  have hr : r.val = a ∨ r.val = a + 1 ∨ (r.val ≠ a ∧ r.val ≠ a + 1) := by omega
  have hs : s.val = a ∨ s.val = a + 1 ∨ (s.val ≠ a ∧ s.val ≠ a + 1) := by omega
  rcases hr with hr | hr | ⟨hr1, hr2⟩ <;> rcases hs with hs | hs | ⟨hs1, hs2⟩ <;>
    first
    | rw [dite_eq_left (by omega)]
    | rw [dite_eq_right (by omega)]
  all_goals
    simp [dMat, dVec, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff, *]
  all_goals (split_ifs <;> first | rfl | omega)

end Algebra

section Elements

variable {F : Type} [Field F] [Finite F] [hF3 : Fact (Nat.card F = 3)]

theorem gaussSigma_omega :
    gaussSigma (F := F) QuadraticAlgebra.omega = -QuadraticAlgebra.omega := by
  rw [gaussSigma_apply]
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]

theorem gaussSigma_neg_one : gaussSigma (F := F) (-1) = -1 := by
  rw [gaussSigma_apply]
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem conjTr_dMat_mul : conjTr (gaussSigma (F := F)) dMat * dMat = 1 := by
  set σ : GaussField F ≃+* GaussField F := gaussSigma with hσ
  have h1 : σ QuadraticAlgebra.omega = -QuadraticAlgebra.omega := gaussSigma_omega
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, dMat, Matrix.mul_apply, Fin.sum_univ_two, h1, omega_mul_omega]

theorem conjTr_wMat_mul : conjTr (gaussSigma (F := F)) wMat * wMat = 1 := by
  set σ : GaussField F ≃+* GaussField F := gaussSigma with hσ
  have h1 : σ (-1) = -1 := gaussSigma_neg_one
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, wMat, Matrix.mul_apply, Fin.sum_univ_two, h1]

@[expose] noncomputable def mkSU {m : ℕ} (M : Matrix (Fin m) (Fin m) (GaussField F))
    (hdet : M.det = 1) (hu : conjTr (gaussSigma (F := F)) M * M = 1) :
    SUid (gaussSigma (F := F)) m :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero), hdet, hu⟩

theorem coe_mkSU {m : ℕ} (M : Matrix (Fin m) (Fin m) (GaussField F)) (hdet : M.det = 1)
    (hu : conjTr (gaussSigma (F := F)) M * M = 1) :
    (((mkSU M hdet hu : SUid (gaussSigma (F := F)) m) : GL (Fin m) (GaussField F)) :
      Matrix (Fin m) (Fin m) (GaussField F)) = M := rfl

theorem two_ne_zero_gauss : (2 : GaussField F) ≠ 0 := by
  have := charP_gaussField (F := F)
  intro h
  have h' : ((2 : ℕ) : GaussField F) = 0 := by exact_mod_cast h
  have := (CharP.cast_eq_zero_iff (GaussField F) 3 2).mp h'
  omega

end Elements

section Commutant

variable {F : Type} [Field F] [Finite F] [hF3 : Fact (Nat.card F = 3)] {m : ℕ}

theorem dVec_ne {a : ℕ} {r s : Fin m} (hr : r.val = a ∨ r.val = a + 1) (hrs : r ≠ s) :
    dVec (F := F) m a r ≠ dVec m a s := by
  obtain ⟨h1, h2, h3⟩ := omega_ne_one_aux (two_ne_zero_gauss (F := F))
  have hn1 : -(QuadraticAlgebra.omega : GaussField F) ≠ 1 := fun h =>
    h2 (neg_eq_iff_eq_neg.mp h)
  have hrs' : r.val ≠ s.val := fun h => hrs (Fin.ext h)
  unfold dVec
  rcases hr with hr | hr
  · rw [ite_eq_left hr]
    by_cases hs : s.val = a
    · omega
    · rw [ite_eq_right hs]
      by_cases hs' : s.val = a + 1
      · rw [ite_eq_left hs']
        exact h3
      · rw [ite_eq_right hs']
        exact h1
  · have hr' : ¬ r.val = a := by omega
    rw [ite_eq_right hr', ite_eq_left hr]
    by_cases hs : s.val = a
    · rw [ite_eq_left hs]
      exact fun h => h3 h.symm
    · rw [ite_eq_right hs]
      by_cases hs' : s.val = a + 1
      · omega
      · rw [ite_eq_right hs']
        exact hn1

theorem entry_eq_zero_of_commute_dBlock {ν : Matrix (Fin m) (Fin m) (GaussField F)} {a : ℕ}
    (h : ν * blockMat m a dMat = blockMat m a dMat * ν) {r s : Fin m}
    (hrs : dVec (F := F) m a r ≠ dVec m a s) : ν r s = 0 := by
  rw [blockMat_dMat] at h
  have h1 := congrFun (congrFun h r) s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : ν r s * (dVec m a s - dVec m a r) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hrs.symm)

theorem blockMat_wMat_col {a : ℕ} (ha : a + 2 ≤ m) (t : Fin m) :
    blockMat m a (wMat (F := F)) t ⟨a + 1, by omega⟩ = if t.val = a then -1 else 0 := by
  rw [blockMat_apply]
  by_cases h1 : t.val = a
  · rw [dite_eq_left (by simp only; omega), ite_eq_left h1]
    have : (⟨t.val - a, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp; omega)
    simp [wMat, this]
  · rw [ite_eq_right h1]
    by_cases h2 : t.val = a + 1
    · rw [dite_eq_left (by simp only; omega)]
      have : (⟨t.val - a, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
      simp [wMat, this]
    · rw [dite_eq_right (by simp only; omega)]
      simp [Matrix.one_apply, Fin.ext_iff]
      omega

theorem blockMat_wMat_row {a : ℕ} (ha : a + 2 ≤ m) (t : Fin m) :
    blockMat m a (wMat (F := F)) ⟨a, by omega⟩ t = if t.val = a + 1 then -1 else 0 := by
  rw [blockMat_apply]
  by_cases h1 : t.val = a + 1
  · rw [dite_eq_left (by simp only; omega), ite_eq_left h1]
    have : (⟨t.val - a, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
    simp [wMat, this]
  · rw [ite_eq_right h1]
    by_cases h2 : t.val = a
    · rw [dite_eq_left (by simp only; omega)]
      have : (⟨t.val - a, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp; omega)
      simp [wMat, this]
    · rw [dite_eq_right (by simp only; omega)]
      simp [Matrix.one_apply, Fin.ext_iff]
      omega

theorem diag_succ_eq_of_commute_wBlock {ν : Matrix (Fin m) (Fin m) (GaussField F)} {a : ℕ}
    (ha : a + 2 ≤ m) (h : ν * blockMat m a wMat = blockMat m a wMat * ν) :
    ν ⟨a, by omega⟩ ⟨a, by omega⟩ = ν ⟨a + 1, by omega⟩ ⟨a + 1, by omega⟩ := by
  have h1 := congrFun (congrFun h ⟨a, by omega⟩) ⟨a + 1, by omega⟩
  rw [Matrix.mul_apply, Matrix.mul_apply] at h1
  simp only [blockMat_wMat_col ha, blockMat_wMat_row ha] at h1
  rw [Finset.sum_eq_single (⟨a, by omega⟩ : Fin m)
      (fun t _ ht => by rw [ite_eq_right (fun h' => ht (Fin.ext h')), mul_zero])
      (fun h' => absurd (Finset.mem_univ _) h'),
    Finset.sum_eq_single (⟨a + 1, by omega⟩ : Fin m)
      (fun t _ ht => by rw [ite_eq_right (fun h' => ht (Fin.ext h')), zero_mul])
      (fun h' => absurd (Finset.mem_univ _) h')] at h1
  simp only [ite_true] at h1
  linear_combination -h1

theorem entry_eq_zero_of_commute_dBlocks {ν : Matrix (Fin m) (Fin m) (GaussField F)} {j k : ℕ}
    (hD : ∀ a, j ≤ a → a + 2 ≤ j + k → ν * blockMat m a dMat = blockMat m a dMat * ν)
    (hk : 2 ≤ k) {r s : Fin m} (hrs : r ≠ s) (hr : j ≤ r.val ∧ r.val < j + k) :
    ν r s = 0 ∧ ν s r = 0 := by
  obtain ⟨a, ha1, ha2, ha3⟩ : ∃ a, j ≤ a ∧ a + 2 ≤ j + k ∧ (r.val = a ∨ r.val = a + 1) := by
    by_cases h : r.val + 1 < j + k
    · exact ⟨r.val, hr.1, by omega, Or.inl rfl⟩
    · exact ⟨r.val - 1, by omega, by omega, Or.inr (by omega)⟩
  have hc := hD a ha1 ha2
  exact ⟨entry_eq_zero_of_commute_dBlock hc (dVec_ne ha3 hrs),
    entry_eq_zero_of_commute_dBlock hc (dVec_ne ha3 hrs).symm⟩

theorem diag_eq_of_commute_wBlocks {ν : Matrix (Fin m) (Fin m) (GaussField F)} {j k : ℕ}
    (hjk : j + k ≤ m)
    (hW : ∀ a, j ≤ a → a + 2 ≤ j + k → ν * blockMat m a wMat = blockMat m a wMat * ν) :
    ∀ n : ℕ, ∀ r : Fin m, j ≤ r.val → ∀ hn : r.val + n < j + k,
      ν r r = ν ⟨r.val + n, by omega⟩ ⟨r.val + n, by omega⟩ := by
  intro n
  induction n with
  | zero => intro r _ _; rfl
  | succ n ih =>
    intro r hr1 hr2
    have h1 := ih r hr1 (by omega)
    have h2 := diag_succ_eq_of_commute_wBlock (ν := ν) (a := r.val + n) (by omega)
      (hW _ (by omega) (by omega))
    exact h1.trans h2

theorem diag_eq_of_commute_wBlocks' {ν : Matrix (Fin m) (Fin m) (GaussField F)} {j k : ℕ}
    (hjk : j + k ≤ m)
    (hW : ∀ a, j ≤ a → a + 2 ≤ j + k → ν * blockMat m a wMat = blockMat m a wMat * ν)
    {r s : Fin m} (hr : j ≤ r.val ∧ r.val < j + k) (hs : j ≤ s.val ∧ s.val < j + k) :
    ν r r = ν s s := by
  rcases le_total r.val s.val with h | h
  · have := diag_eq_of_commute_wBlocks hjk hW (s.val - r.val) r hr.1 (by omega)
    convert this using 2 <;> exact Fin.ext (by simp; omega)
  · have := diag_eq_of_commute_wBlocks hjk hW (r.val - s.val) s hs.1 (by omega)
    convert this.symm using 2 <;> exact Fin.ext (by simp; omega)

theorem commute_blockMat_of_commute_su {ν : Matrix (Fin m) (Fin m) (GaussField F)}
    (h : ∀ X : SUid (gaussSigma (F := F)) m,
      ν * ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) =
        ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) * ν)
    {a : ℕ} (ha : a + 2 ≤ m) :
    ν * blockMat m a dMat = blockMat m a dMat * ν ∧
      ν * blockMat m a wMat = blockMat m a wMat * ν := by
  have hD := h (blockEmb (GaussField F) 3 1 m 2 a ha (mkSU dMat det_dMat conjTr_dMat_mul))
  have hW := h (blockEmb (GaussField F) 3 1 m 2 a ha (mkSU wMat det_wMat conjTr_wMat_mul))
  rw [coe_coe_blockEmb, coe_mkSU] at hD hW
  exact ⟨hD, hW⟩

theorem exists_scalar_of_commute_su (hm : 2 ≤ m) {ν : Matrix (Fin m) (Fin m) (GaussField F)}
    (h : ∀ X : SUid (gaussSigma (F := F)) m,
      ν * ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) =
        ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) * ν) :
    ∃ c : GaussField F, ν = Matrix.scalar (Fin m) c := by
  have hD : ∀ a, 0 ≤ a → a + 2 ≤ 0 + m →
      ν * blockMat m a dMat = blockMat m a dMat * ν := fun a _ ha =>
    (commute_blockMat_of_commute_su h (by omega)).1
  have hW : ∀ a, 0 ≤ a → a + 2 ≤ 0 + m →
      ν * blockMat m a wMat = blockMat m a wMat * ν := fun a _ ha =>
    (commute_blockMat_of_commute_su h (by omega)).2
  refine ⟨ν ⟨0, by omega⟩ ⟨0, by omega⟩, Matrix.ext fun r s => ?_⟩
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact diag_eq_of_commute_wBlocks' (by omega) hW (by simp) (by simp; omega)
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hrs]
    exact (entry_eq_zero_of_commute_dBlocks hD hm hrs (by simp)).1

end Commutant

end CFSG.ClassicalInvolution.Q3
