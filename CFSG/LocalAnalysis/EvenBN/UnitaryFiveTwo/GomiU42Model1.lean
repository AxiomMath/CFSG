module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KSix
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup CFSG.Fischer

@[expose] def m1Diag : Fin 5 → F4 := ![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω]

theorem e₂Mat_eq_diagonal : e₂Mat = Matrix.diagonal m1Diag := rfl

theorem m1Diag_of_ne : ∀ i : Fin 5, i ≠ 2 → m1Diag i = F4.ω := by decide

theorem m1_offdiag_zero : ∀ (i j : Fin 5) (x : F4), i ≠ j → (i = 2 ∨ j = 2) →
    x * m1Diag j = m1Diag i * x → x = 0 := by
  decide

theorem m1_extMat_cross (y : Matrix (Fin 4) (Fin 4) F4) (i : Fin 5) (hi : i ≠ 2) :
    extMat y i 2 = 0 ∧ extMat y 2 i = 0 := by
  fin_cases i <;> first | exact ⟨rfl, rfl⟩ | exact absurd rfl hi

theorem m1_zeros_of_eq_extMat {M : Matrix (Fin 5) (Fin 5) F4} (hM : M = extMat (subMat M)) :
    ∀ i : Fin 5, i ≠ 2 → M i 2 = 0 ∧ M 2 i = 0 := fun i hi =>
  ⟨(congrFun (congrFun hM i) 2).trans (m1_extMat_cross _ i hi).1,
    (congrFun (congrFun hM 2) i).trans (m1_extMat_cross _ i hi).2⟩

theorem m1_eq_extMat_of {M : Matrix (Fin 5) (Fin 5) F4}
    (h : ∀ i : Fin 5, i ≠ 2 → M i 2 = 0 ∧ M 2 i = 0) (h22 : M 2 2 = 1) :
    M = extMat (subMat M) := by
  obtain ⟨h0a, h0b⟩ := h 0 (by decide)
  obtain ⟨h1a, h1b⟩ := h 1 (by decide)
  obtain ⟨h3a, h3b⟩ := h 3 (by decide)
  obtain ⟨h4a, h4b⟩ := h 4 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extMat, subMat, h0a, h0b, h1a, h1b, h3a, h3b, h4a, h4b, h22]

theorem m1_mem_StabSub_of_zeros {g : SU52}
    (h : ∀ i : Fin 5, i ≠ 2 → mat g i 2 = 0 ∧ mat g 2 i = 0) (h22 : mat g 2 2 = 1) :
    g ∈ StabSub :=
  mem_StabSub.2 (m1_eq_extMat_of h h22)

theorem m1_22_of_mem_StabSub {g : SU52} (hg : g ∈ StabSub) : mat g 2 2 = 1 :=
  (congrFun (congrFun (mem_StabSub.1 hg) 2) 2).trans rfl

theorem m1_entry_comm {M : Matrix (Fin 5) (Fin 5) F4} (hM : M * e₂Mat = e₂Mat * M) (i j : Fin 5) :
    M i j * m1Diag j = m1Diag i * M i j := by
  have e := congrFun (congrFun hM i) j
  rw [e₂Mat_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  exact e

theorem m1_zeros_of_comm {M : Matrix (Fin 5) (Fin 5) F4} (hM : M * e₂Mat = e₂Mat * M) :
    ∀ i : Fin 5, i ≠ 2 → M i 2 = 0 ∧ M 2 i = 0 := fun i hi =>
  ⟨m1_offdiag_zero i 2 _ hi (Or.inr rfl) (m1_entry_comm hM i 2),
    m1_offdiag_zero 2 i _ (Ne.symm hi) (Or.inl rfl) (m1_entry_comm hM 2 i)⟩

theorem m1_mul_e₂Mat_comm {M : Matrix (Fin 5) (Fin 5) F4}
    (h : ∀ i : Fin 5, i ≠ 2 → M i 2 = 0 ∧ M 2 i = 0) : M * e₂Mat = e₂Mat * M := by
  ext i j
  rw [e₂Mat_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i = 2
  · subst hi
    by_cases hj : j = 2
    · subst hj
      exact mul_comm _ _
    · simp [(h j hj).2]
  · by_cases hj : j = 2
    · subst hj
      simp [(h i hi).1]
    · rw [m1Diag_of_ne i hi, m1Diag_of_ne j hj]
      exact mul_comm _ _

theorem commute_e₂SU_of_mem_StabSub {g : SU52} (hg : g ∈ StabSub) : g * e₂SU = e₂SU * g := by
  refine ext_mat ?_
  rw [mat_mul, mat_mul, mat_e₂SU]
  exact m1_mul_e₂Mat_comm (m1_zeros_of_eq_extMat (mem_StabSub.1 hg))

theorem m1_mat_pow (g : SU52) (k : ℕ) : mat (g ^ k) = mat g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem m1_mat_mul_e₂SU_pow (g : SU52) (k : ℕ) (i j : Fin 5) :
    mat (g * e₂SU ^ k) i j = mat g i j * m1Diag j ^ k := by
  rw [mat_mul, m1_mat_pow, mat_e₂SU, e₂Mat_eq_diagonal, Matrix.diagonal_pow, Matrix.mul_diagonal]
  all_goals rfl

theorem zpowers_e₂SU_inf_StabSub : zpowers e₂SU ⊓ StabSub = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hz, hs⟩ := hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have hmod : e₂SU ^ (k % (3 : ℕ)) = e₂SU ^ k := by
    rw [← orderOf_e₂SU]
    exact zpow_mod_orderOf e₂SU k
  have key : ∀ m : ℤ, 0 ≤ m → m < 3 → e₂SU ^ m ∈ StabSub → e₂SU ^ m = 1 := by
    intro m h0 h3 hm
    interval_cases m
    · exact zpow_zero _
    · exfalso
      have h := m1_22_of_mem_StabSub hm
      rw [zpow_one, mat_e₂SU] at h
      exact absurd h (by decide)
    · exfalso
      have h := m1_22_of_mem_StabSub hm
      rw [zpow_two, mat_mul, mat_e₂SU] at h
      exact absurd h (by decide)
  rw [Subgroup.mem_bot, ← hmod]
  exact key (k % (3 : ℕ)) (Int.emod_nonneg _ (by norm_num))
    (Int.emod_lt_of_pos _ (by norm_num)) (by rw [hmod]; exact hs)

theorem m1_unit_22 {M : Matrix (Fin 5) (Fin 5) F4} (h : (M.map bar)ᵀ * J5 * M = J5)
    (h0 : ∀ i : Fin 5, i ≠ 2 → M i 2 = 0) : bar (M 2 2) * M 2 2 = 1 := by
  have hA : ((M.map bar)ᵀ * J5) 2 2 = bar (M 2 2) := by
    simp [Matrix.mul_apply, Fin.sum_univ_five, J5]
  have e := congrFun (congrFun h 2) 2
  rw [Matrix.mul_apply, Fin.sum_univ_five, h0 0 (by decide), h0 1 (by decide),
    h0 3 (by decide), h0 4 (by decide), hA] at e
  have hJ : J5 2 2 = 1 := by decide
  rw [hJ] at e
  simpa using e

theorem centralizer_e₂SU_eq : centralizer ({e₂SU} : Set SU52) = zpowers e₂SU ⊔ StabSub := by
  apply le_antisymm
  · intro g hg
    rw [mem_centralizer_singleton_iff] at hg
    have hm : mat g * e₂Mat = e₂Mat * mat g := by
      have h := congrArg mat hg
      rwa [mat_mul, mat_mul, mat_e₂SU] at h
    have hcr := m1_zeros_of_comm hm
    have hu : bar (mat g 2 2) * mat g 2 2 = 1 :=
      m1_unit_22 (mem_SU52.1 g.2).1 (fun i hi => (hcr i hi).1)
    have hcases : ∀ c : F4, bar c * c = 1 → c = 1 ∨ c = F4.ω ∨ c = bar F4.ω := by decide
    obtain ⟨k, hk⟩ : ∃ k : ℕ, mat g 2 2 * bar F4.ω ^ k = 1 := by
      rcases hcases _ hu with h | h | h
      · exact ⟨0, by rw [h, pow_zero, mul_one]⟩
      · exact ⟨1, by rw [h]; decide⟩
      · exact ⟨2, by rw [h]; decide⟩
    have hgz : g * e₂SU ^ k ∈ StabSub := by
      refine m1_mem_StabSub_of_zeros (fun i hi => ⟨?_, ?_⟩) ?_
      · rw [m1_mat_mul_e₂SU_pow, (hcr i hi).1, zero_mul]
      · rw [m1_mat_mul_e₂SU_pow, (hcr i hi).2, zero_mul]
      · rw [m1_mat_mul_e₂SU_pow]
        exact hk
    have h : g * e₂SU ^ k * (e₂SU ^ k)⁻¹ ∈ zpowers e₂SU ⊔ StabSub :=
      mul_mem (mem_sup_right hgz) (mem_sup_left (inv_mem (pow_mem (mem_zpowers e₂SU) k)))
    rwa [mul_inv_cancel_right] at h
  · refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) ?_
    intro g hg
    exact mem_centralizer_singleton_iff.2 (commute_e₂SU_of_mem_StabSub hg)

theorem m1_mat_inv_mul (g : SU52) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem not_conj_e₂SU_inv (g : SU52) : g * e₂SU * g⁻¹ ≠ e₂SU⁻¹ := by
  intro h
  have hinv : mat e₂SU⁻¹ = Matrix.diagonal ![bar F4.ω, bar F4.ω, F4.ω, bar F4.ω, bar F4.ω] :=
    mat_inv_eq (by rw [mat_e₂SU, e₂Mat_eq_diagonal]; decide)
  have ht := congrArg (fun x : SU52 => Matrix.trace (mat x)) h
  simp only [mat_mul] at ht
  rw [Matrix.trace_mul_cycle, m1_mat_inv_mul, one_mul, mat_e₂SU, hinv] at ht
  exact absurd ht (by decide)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
