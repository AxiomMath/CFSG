module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.Foundations.Basic
import CFSG.RankThree.PartOne.KF.LayerGen
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

section TwoByTwo

variable {K : Type*} [Field K]

theorem exists_eq_smul_one_add_smul_of_mul_eq_mul {x M : Matrix (Fin 2) (Fin 2) K}
    (hx : ¬ (x 0 1 = 0 ∧ x 1 0 = 0 ∧ x 0 0 = x 1 1)) (hM : M * x = x * M) :
    ∃ s r : K, M = s • (1 : Matrix (Fin 2) (Fin 2) K) + r • x := by
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases hb : x 0 1 = 0
  · by_cases hc : x 1 0 = 0
    · have hd : x 0 0 - x 1 1 ≠ 0 := sub_ne_zero.2 fun h => hx ⟨hb, hc, h⟩
      have h01 : M 0 1 = 0 := by
        have : M 0 1 * (x 0 0 - x 1 1) = 0 := by
          rw [hb] at e01; linear_combination -e01
        exact (mul_eq_zero.1 this).resolve_right hd
      have h10 : M 1 0 = 0 := by
        have : M 1 0 * (x 0 0 - x 1 1) = 0 := by
          rw [hc] at e10; linear_combination e10
        exact (mul_eq_zero.1 this).resolve_right hd
      refine ⟨M 0 0 - (M 0 0 - M 1 1) / (x 0 0 - x 1 1) * x 0 0,
        (M 0 0 - M 1 1) / (x 0 0 - x 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, h01, h10]
      field_simp
      ring
    · refine ⟨M 0 0 - M 1 0 / x 1 0 * x 0 0, M 1 0 / x 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · field_simp
        linear_combination e00
      · field_simp
      · field_simp
        linear_combination e10
  · refine ⟨M 0 0 - M 0 1 / x 0 1 * x 0 0, M 0 1 / x 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · field_simp
    · field_simp
      linear_combination -e00
    · field_simp
      linear_combination -e01

theorem mul_comm_of_mul_eq_mul {x M N : Matrix (Fin 2) (Fin 2) K}
    (hx : ¬ (x 0 1 = 0 ∧ x 1 0 = 0 ∧ x 0 0 = x 1 1)) (hM : M * x = x * M) (hN : N * x = x * N) :
    M * N = N * M := by
  obtain ⟨s, r, rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hx hM
  obtain ⟨s', r', rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hx hN
  have h : Commute (s • (1 : Matrix (Fin 2) (Fin 2) K) + r • x) (s' • 1 + r' • x) :=
    (((Commute.one_left _).smul_left s).add_left
      ((((Commute.one_right x).smul_right s').add_right
        ((Commute.refl x).smul_right r')).smul_left r))
  exact h.eq

end TwoByTwo


section Block

variable {K : Type*} [Field K] {n : ℕ}

theorem blockDiag_of_agrees_one {J : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j) :
    ∀ i j, (i ∈ J ↔ j ∉ J) → M i j = 0 := by
  intro i j hij
  have hne : i ≠ j := by
    rintro rfl
    tauto
  rw [hM i j (by tauto), one_apply_ne hne]

theorem blockDiag_mul {J : Finset (Fin n)} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∈ J ↔ j ∉ J) → M i j = 0) (hN : ∀ i j, (i ∈ J ↔ j ∉ J) → N i j = 0) :
    ∀ i j, (i ∈ J ↔ j ∉ J) → (M * N) i j = 0 := by
  intro i j hij
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ∈ J
  · by_cases hi : i ∈ J
    · rw [hN k j (by tauto), mul_zero]
    · rw [hM i k (by tauto), zero_mul]
  · by_cases hi : i ∈ J
    · rw [hM i k (by tauto), zero_mul]
    · rw [hN k j (by tauto), mul_zero]

theorem submatrix_mul_of_rows {r : ℕ} {e : Fin r → Fin n} (he : Function.Injective e)
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i ∈ J, ∀ k ∉ J, M i k = 0) (N : Matrix (Fin n) (Fin n) K) :
    (M * N).submatrix e e = M.submatrix e e * N.submatrix e e := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  refine (Fintype.sum_of_injective e he _ _ (fun k hk => ?_) fun k => rfl).symm
  rw [hM (e i) ((hJ _).2 ⟨i, rfl⟩) k fun h => hk ((hJ k).1 h), zero_mul]

theorem det_submatrix_of_agrees_one {r : ℕ} {e : Fin r → Fin n} (he : Function.Injective e)
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j) :
    (M.submatrix e e).det = M.det := by
  classical
  rw [M.twoBlockTriangular_det' (fun s => s ∈ Set.range e) fun a ha b hb => by
    rw [hM a b (Or.inr fun h => hb ((hJ b).1 h)),
      one_apply_ne (show a ≠ b from fun h => hb (h ▸ ha))]]
  have h1 : M.toSquareBlockProp (fun s => s ∉ Set.range e) = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    rw [toSquareBlockProp, Matrix.toBlock_apply, hM a b (Or.inl fun h => ha ((hJ a).1 h)),
      one_apply, one_apply]
    simp only [Subtype.mk.injEq]
  rw [h1, det_one, mul_one]
  convert det_submatrix_equiv_self (Equiv.ofInjective e he)
    (M.toSquareBlockProp fun s => s ∈ Set.range e) using 2
  rfl

theorem commutator_agrees_one_compl {r : ℕ} {e : Fin r → Fin n} (he : Function.Injective e)
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e)
    {𝒞 : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hdiag : ∀ A ∈ 𝒞, ∀ i j, (i ∈ J ↔ j ∉ J) → (A : Matrix (Fin n) (Fin n) K) i j = 0)
    (hcomm : ∀ A ∈ 𝒞, ∀ B ∈ 𝒞, (A : Matrix (Fin n) (Fin n) K).submatrix e e *
      (B : Matrix (Fin n) (Fin n) K).submatrix e e =
        (B : Matrix (Fin n) (Fin n) K).submatrix e e * (A : Matrix (Fin n) (Fin n) K).submatrix e e)
    {A B : SpecialLinearGroup (Fin n) K} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) :
    ∀ i j, (i ∉ Jᶜ ∨ j ∉ Jᶜ) → ((A * B * A⁻¹ * B⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  have hrows : ∀ X ∈ 𝒞, ∀ i ∈ J, ∀ k ∉ J, (X : Matrix (Fin n) (Fin n) K) i k = 0 :=
    fun X hX i hi k hk => hdiag X hX i k (by tauto)
  have hsub : ∀ X ∈ 𝒞, ∀ Y : SpecialLinearGroup (Fin n) K,
      ((X * Y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix e e =
        (X : Matrix (Fin n) (Fin n) K).submatrix e e *
          (Y : Matrix (Fin n) (Fin n) K).submatrix e e := fun X hX Y => by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact submatrix_mul_of_rows he hJ (hrows X hX) _
  have hAi : A⁻¹ ∈ 𝒞 := inv_mem hA
  have hBi : B⁻¹ ∈ 𝒞 := inv_mem hB
  have hone : ∀ X ∈ 𝒞, (X : Matrix (Fin n) (Fin n) K).submatrix e e *
      ((X⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix e e = 1 :=
    fun X hX => by
      rw [← hsub X hX, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, submatrix_one _ he]
  have hblock : ((A * B * A⁻¹ * B⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).submatrix e e = 1 := by
    rw [hsub _ (mul_mem (mul_mem hA hB) hAi), hsub _ (mul_mem hA hB), hsub _ hA,
      Matrix.mul_assoc ((A : Matrix (Fin n) (Fin n) K).submatrix e e),
      hcomm B hB A⁻¹ hAi, ← Matrix.mul_assoc, hone A hA, Matrix.one_mul, hone B hB]
  have hC : A * B * A⁻¹ * B⁻¹ ∈ 𝒞 := mul_mem (mul_mem (mul_mem hA hB) hAi) hBi
  intro i j hij
  simp only [Finset.mem_compl, not_not] at hij
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · obtain ⟨k, rfl⟩ := (hJ i).1 hi
    obtain ⟨l, rfl⟩ := (hJ j).1 hj
    have := congrFun (congrFun hblock k) l
    rw [submatrix_apply] at this
    rw [this]
    by_cases hkl : k = l
    · subst hkl
      simp
    · rw [one_apply_ne hkl, one_apply_ne (he.ne hkl)]
  · rw [hdiag _ hC i j (by tauto), one_apply_ne (fun h : i = j => hj (h ▸ hi))]
  · rw [hdiag _ hC i j (by tauto), one_apply_ne (fun h : i = j => hi (h ▸ hj))]
  · tauto

end Block


section Pair

variable {K : Type*} [Field K] {n : ℕ} {a b : Fin n}

theorem mem_pair_iff_mem_range (i : Fin n) :
    i ∈ ({a, b} : Finset (Fin n)) ↔ i ∈ Set.range ![a, b] := by
  constructor
  · intro h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact ⟨0, rfl⟩
    · rw [Finset.mem_singleton.1 h]
      exact ⟨1, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp

theorem pair_injective (hab : a ≠ b) : Function.Injective ![a, b] := by
  intro k l h
  fin_cases k <;> fin_cases l <;> simp_all [eq_comm]

theorem mul_apply_eq_of_row (hab : a ≠ b) {M : Matrix (Fin n) (Fin n) K} {i : Fin n}
    (hM : ∀ k ∉ ({a, b} : Finset (Fin n)), M i k = 0) (N : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    (M * N) i j = M i a * N a j + M i b * N b j := by
  rw [mul_apply]
  exact Fintype.sum_eq_add a b hab fun k hk => by
    rw [hM k (by simp [hk.1, hk.2]), zero_mul]

variable {x : Matrix (Fin n) (Fin n) K}

theorem row_eq_zero_of_agrees_one
    (hx : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      x i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    {i : Fin n} (hi : i ∈ ({a, b} : Finset (Fin n))) : ∀ k ∉ ({a, b} : Finset (Fin n)), x i k = 0 :=
  fun k hk => by rw [hx i k (Or.inr hk), one_apply_ne (fun h : i = k => hk (h ▸ hi))]

theorem det_eq_of_agrees_one_pair (hab : a ≠ b)
    (hx : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      x i j = (1 : Matrix (Fin n) (Fin n) K) i j) :
    x.det = x a a * x b b - x a b * x b a := by
  rw [← det_submatrix_of_agrees_one (pair_injective hab) mem_pair_iff_mem_range hx, det_fin_two]
  simp

variable [CharP K 2]

theorem eq_zero_of_mulVec_eq_self (hab : a ≠ b)
    (hx : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      x i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (hdet : x.det = 1) (hsq : x * x ≠ 1) {v : Fin n → K} (hv : x *ᵥ v = v) :
    v a = 0 ∧ v b = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hd := det_eq_of_agrees_one_pair hab hx
  rw [hdet] at hd
  have hrowa := row_eq_zero_of_agrees_one hx (by simp : a ∈ ({a, b} : Finset (Fin n)))
  have hrowb := row_eq_zero_of_agrees_one hx (by simp : b ∈ ({a, b} : Finset (Fin n)))
  have hva : x a a * v a + x a b * v b = v a := by
    have := congrFun hv a
    rw [mulVec, dotProduct, Fintype.sum_eq_add a b hab fun k hk => by
      rw [hrowa k (by simp [hk.1, hk.2]), zero_mul]] at this
    exact this
  have hvb : x b a * v a + x b b * v b = v b := by
    have := congrFun hv b
    rw [mulVec, dotProduct, Fintype.sum_eq_add a b hab fun k hk => by
      rw [hrowb k (by simp [hk.1, hk.2]), zero_mul]] at this
    exact this
  by_contra hne
  have hD : (x a a - 1) * (x b b - 1) - x a b * x b a = 0 := by
    by_cases ha : v a = 0
    · have hb : v b ≠ 0 := fun hb => hne ⟨ha, hb⟩
      refine (mul_eq_zero.1
        (?_ : ((x a a - 1) * (x b b - 1) - x a b * x b a) * v b = 0)).resolve_right hb
      linear_combination (x a a - 1) * hvb - x b a * hva
    · refine (mul_eq_zero.1
        (?_ : ((x a a - 1) * (x b b - 1) - x a b * x b a) * v a = 0)).resolve_right ha
      linear_combination (x b b - 1) * hva - x a b * hvb
  have htr : x a a + x b b = 0 := by linear_combination -hD - hd + h2
  apply hsq
  ext i j
  by_cases hi : i ∈ ({a, b} : Finset (Fin n))
  · by_cases hj : j ∈ ({a, b} : Finset (Fin n))
    · rw [mul_apply_eq_of_row hab (row_eq_zero_of_agrees_one hx hi)]
      have hi2 : i = a ∨ i = b := by simpa using hi
      have hj2 : j = a ∨ j = b := by simpa using hj
      rcases hi2 with hia | hib <;> rcases hj2 with hja | hjb
      · rw [hia, hja, one_apply_eq]
        linear_combination (x a a) * htr + hd - h2
      · rw [hia, hjb, one_apply_ne hab]
        linear_combination (x a b) * htr
      · rw [hib, hja, one_apply_ne hab.symm]
        linear_combination (x b a) * htr
      · rw [hib, hjb, one_apply_eq]
        linear_combination (x b b) * htr + hd - h2
    · have hcol : ∀ k, x k j = (1 : Matrix (Fin n) (Fin n) K) k j := fun k => hx k j (Or.inr hj)
      rw [mul_apply, Finset.sum_congr rfl fun k _ => by rw [hcol k], ← mul_apply, Matrix.mul_one,
        hx i j (Or.inr hj)]
  · have hrow : ∀ k, x i k = (1 : Matrix (Fin n) (Fin n) K) i k := fun k => hx i k (Or.inl hi)
    rw [mul_apply, Finset.sum_congr rfl fun k _ => by rw [hrow k], ← mul_apply, Matrix.one_mul,
      hx i j (Or.inl hi)]

omit [CharP K 2] in
theorem transpose_agrees_one {J : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j) :
    ∀ i j, (i ∉ J ∨ j ∉ J) → Mᵀ i j = (1 : Matrix (Fin n) (Fin n) K) i j := fun i j h => by
  rw [transpose_apply, hM j i h.symm, ← transpose_apply (1 : Matrix (Fin n) (Fin n) K) i j,
    transpose_one]

theorem blockDiag_of_mul_eq_mul (hab : a ≠ b)
    (hx : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      x i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (hdet : x.det = 1) (hsq : x * x ≠ 1) {A : Matrix (Fin n) (Fin n) K} (hA : A * x = x * A) :
    ∀ i j, (i ∈ ({a, b} : Finset (Fin n)) ↔ j ∉ ({a, b} : Finset (Fin n))) → A i j = 0 := by
  intro i j hij
  by_cases hi : i ∈ ({a, b} : Finset (Fin n))
  · have hj : j ∉ ({a, b} : Finset (Fin n)) := hij.1 hi
    have hv : x *ᵥ (fun k => A k j) = fun k => A k j := by
      ext k
      have h1 := congrFun (congrFun hA k) j
      have hcol : (A * x) k j = A k j := by
        rw [mul_apply, Finset.sum_congr rfl fun l _ => by rw [hx l j (Or.inr hj)], ← mul_apply,
          Matrix.mul_one]
      rw [hcol, mul_apply] at h1
      simp only [mulVec, dotProduct]
      exact h1.symm
    obtain ⟨ha, hb⟩ := eq_zero_of_mulVec_eq_self hab hx hdet hsq hv
    have hi2 : i = a ∨ i = b := by simpa using hi
    rcases hi2 with rfl | rfl
    · exact ha
    · exact hb
  · have hj : j ∈ ({a, b} : Finset (Fin n)) := by tauto
    have hxT := transpose_agrees_one hx
    have hdetT : xᵀ.det = 1 := by rw [det_transpose, hdet]
    have hsqT : xᵀ * xᵀ ≠ 1 := by
      intro h
      apply hsq
      rw [← transpose_mul] at h
      rw [← transpose_transpose (x * x), h, transpose_one]
    have hv : xᵀ *ᵥ (fun k => A i k) = fun k => A i k := by
      ext k
      have h1 := congrFun (congrFun hA i) k
      have hrow : (x * A) i k = A i k := by
        rw [mul_apply, Finset.sum_congr rfl fun l _ => by rw [hx i l (Or.inl hi)], ← mul_apply,
          Matrix.one_mul]
      rw [hrow, mul_apply] at h1
      simp only [mulVec, dotProduct, transpose_apply]
      rw [← h1]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    obtain ⟨ha, hb⟩ := eq_zero_of_mulVec_eq_self hab hxT hdetT hsqT hv
    have hj2 : j = a ∨ j = b := by simpa using hj
    rcases hj2 with rfl | rfl
    · exact ha
    · exact hb

theorem not_scalar_submatrix_pair (hab : a ≠ b)
    (hx : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      x i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (hdet : x.det = 1) (hsq : x * x ≠ 1) :
    ¬ (x.submatrix ![a, b] ![a, b] 0 1 = 0 ∧ x.submatrix ![a, b] ![a, b] 1 0 = 0 ∧
      x.submatrix ![a, b] ![a, b] 0 0 = x.submatrix ![a, b] ![a, b] 1 1) := by
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rintro ⟨h01, h10, h00⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hd := det_eq_of_agrees_one_pair hab hx
  rw [hdet, h01, h10, ← h00] at hd
  have haa : x a a = 1 := by
    have : (x a a - 1) ^ 2 = 0 := by linear_combination -hd - x a a * h2 + h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  have hv : x *ᵥ Pi.single a 1 = Pi.single a 1 := by
    ext k
    rw [mulVec_single_one, col_apply]
    by_cases hka : k = a
    · rw [hka, haa, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hka]
      by_cases hkb : k = b
      · rw [hkb, h10]
      · rw [hx k a (Or.inl (by simp [hka, hkb])), one_apply_ne hka]
  have := (eq_zero_of_mulVec_eq_self hab hx hdet hsq hv).1
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this

theorem commutator_agrees_one_of_mem_centralizer (hab : a ≠ b) {x : SpecialLinearGroup (Fin n) K}
    (hx : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      (x : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (hsq : x * x ≠ 1) {A B : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)))
    (hB : B ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K))) :
    ∀ i j, (i ∉ ({a, b} : Finset (Fin n))ᶜ ∨ j ∉ ({a, b} : Finset (Fin n))ᶜ) →
      ((A * B * A⁻¹ * B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (1 : Matrix (Fin n) (Fin n) K) i j := by
  have hdet : (x : Matrix (Fin n) (Fin n) K).det = 1 := x.2
  have hsq' : (x : Matrix (Fin n) (Fin n) K) * x ≠ 1 := fun h =>
    hsq (Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_one]))
  have hcomm : ∀ C ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)),
      (C : Matrix (Fin n) (Fin n) K) * x = x * C := fun C hC => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hC
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hC]
  have hdiag : ∀ C ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ i j, (i ∈ ({a, b} : Finset (Fin n)) ↔ j ∉ ({a, b} : Finset (Fin n))) →
        (C : Matrix (Fin n) (Fin n) K) i j = 0 := fun C hC =>
    blockDiag_of_mul_eq_mul hab hx hdet hsq' (hcomm C hC)
  refine commutator_agrees_one_compl (pair_injective hab) mem_pair_iff_mem_range hdiag
    (fun C hC D hD => ?_) hA hB
  have hblock : ∀ E ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)),
      (E : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] *
          (x : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] =
        (x : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] *
          (E : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] := fun E hE => by
    rw [← submatrix_mul_of_rows (pair_injective hab) mem_pair_iff_mem_range
        (fun i hi k hk => hdiag E hE i k (by tauto)),
      ← submatrix_mul_of_rows (pair_injective hab) mem_pair_iff_mem_range
        (fun i hi k hk => row_eq_zero_of_agrees_one hx hi k hk), hcomm E hE]
  exact mul_comm_of_mul_eq_mul (not_scalar_submatrix_pair hab hx hdet hsq') (hblock C hC)
    (hblock D hD)

end Pair


section Lift

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem eq_one_of_pow_card_add_one {c : Kˣ} (hc : c ^ (Nat.card K + 1) = 1) : c = 1 := by
  have hq1 : c ^ (Nat.card K - 1) = 1 := by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hsq : c ^ 2 = 1 := by
    rw [show Nat.card K + 1 = (Nat.card K - 1) + 2 by omega, pow_add, hq1, one_mul] at hc
    exact hc
  have hsq' : (c : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0 : ((c : K) - 1) ^ 2 = 0 := by linear_combination hsq' + (1 - (c : K)) * h2
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))

theorem mul_eq_mul_of_proj_commute {A x : SpecialLinearGroup (Fin n) K}
    (hAx : LinearFlag.proj n K A * LinearFlag.proj n K x =
      LinearFlag.proj n K x * LinearFlag.proj n K A)
    (hx : LinearFlag.proj n K x ^ (Nat.card K + 1) = 1) : A * x = x * A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subtype.ext (Subsingleton.elim _ _)
  set z := (A * x)⁻¹ * (x * A) with hzdef
  have hz : z ∈ LinearFlag.scalars n K := by
    rw [← LinearFlag.proj_eq_proj_iff, map_mul, map_mul, hAx]
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    LinearFlag.scalars_le_center n K hz
  have hxA : x * A = A * x * z := by rw [hzdef, mul_inv_cancel_left]
  have hxm : x ^ (Nat.card K + 1) ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    refine LinearFlag.scalars_le_center n K ?_
    rw [← LinearFlag.ker_proj, MonoidHom.mem_ker, map_pow, hx]
  have h1 : A⁻¹ * x * A = x * z := by
    rw [mul_assoc, hxA]
    group
  have h2 : (A⁻¹ * x * A) ^ (Nat.card K + 1) = x ^ (Nat.card K + 1) := by
    have := conj_pow (a := A⁻¹) (b := x) (i := Nat.card K + 1)
    rw [inv_inv] at this
    rw [this, mul_assoc, (Subgroup.mem_center_iff.1 hxm A).symm, ← mul_assoc, inv_mul_cancel,
      one_mul]
  have h3 : (x * z) ^ (Nat.card K + 1) = x ^ (Nat.card K + 1) * z ^ (Nat.card K + 1) :=
    (show Commute x z from Subgroup.mem_center_iff.1 hzc x).mul_pow _
  rw [h1, h3] at h2
  have hzm : z ^ (Nat.card K + 1) = 1 := by
    have := congrArg (fun w => (x ^ (Nat.card K + 1))⁻¹ * w) h2
    simpa using this
  obtain ⟨c, -, hcz⟩ := LinearFlag.mem_scalars.1 hz
  have hcm : c ^ (Nat.card K + 1) = 1 := by
    have h4 := congrArg (fun w : SpecialLinearGroup (Fin n) K =>
      (w : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hzm
    simp only [Matrix.SpecialLinearGroup.coe_pow, hcz, Matrix.SpecialLinearGroup.coe_one,
      one_apply_eq] at h4
    rw [← map_pow, scalar_apply, diagonal_apply_eq] at h4
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h4, Units.val_one])
  have hc1 : c = 1 := eq_one_of_pow_card_add_one hcm
  have hz1 : z = 1 := Subtype.ext (by rw [hcz, hc1, Units.val_one, map_one,
    Matrix.SpecialLinearGroup.coe_one])
  rw [hxA, hz1, mul_one]

omit [Finite K] [CharP K 2] in
theorem exists_smul_of_proj_eq {Y T : SpecialLinearGroup (Fin n) K}
    (h : LinearFlag.proj n K Y = LinearFlag.proj n K T) :
    ∃ c : Kˣ, (T : Matrix (Fin n) (Fin n) K) = (c : K) • (Y : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 (LinearFlag.proj_eq_proj_iff.1 h)
  refine ⟨c, ?_⟩
  have hT : T = Y * (Y⁻¹ * T) := by group
  rw [hT, Matrix.SpecialLinearGroup.coe_mul, hc, scalar_apply, ← smul_one_eq_diagonal,
    Matrix.mul_smul, Matrix.mul_one]

end Lift

section Singular

variable {K : Type*} [Field K] {n : ℕ}

theorem det_eq_zero_of_cols {A : Matrix (Fin n) (Fin n) K} {c j₁ j₂ : Fin n} (hj : j₁ ≠ j₂)
    (h₁ : ∀ i, i ≠ c → A i j₁ = 0) (h₂ : ∀ i, i ≠ c → A i j₂ = 0) : A.det = 0 := by
  by_contra hA
  have hv : A *ᵥ (Pi.single j₁ (A c j₂) - Pi.single j₂ (A c j₁)) = 0 := by
    ext i
    simp only [mulVec_sub, mulVec_single, Pi.sub_apply, Pi.smul_apply, col_apply,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]
    by_cases hi : i = c
    · rw [hi]
      ring
    · rw [h₁ i hi, h₂ i hi]
      ring
  have h0 := eq_zero_of_mulVec_eq_zero hA hv
  have hc2 : A c j₂ = 0 := by
    have := congrFun h0 j₁
    simpa [Pi.single_apply, hj] using this
  have hc1 : A c j₁ = 0 := by
    have := congrFun h0 j₂
    simpa [Pi.single_apply, hj.symm] using this
  have hcol : A *ᵥ Pi.single j₁ 1 = 0 := by
    ext i
    rw [mulVec_single_one, col_apply, Pi.zero_apply]
    by_cases hi : i = c
    · rw [hi, hc1]
    · exact h₁ i hi
  have := congrFun (eq_zero_of_mulVec_eq_zero hA hcol) j₁
  simp at this

theorem det_eq_zero_of_col {A : Matrix (Fin n) (Fin n) K} {j : Fin n} (h : ∀ i, A i j = 0) :
    A.det = 0 := by
  by_contra hA
  have hcol : A *ᵥ Pi.single j 1 = 0 := by
    ext i
    rw [mulVec_single_one, col_apply, Pi.zero_apply, h i]
  have := congrFun (eq_zero_of_mulVec_eq_zero hA hcol) j
  simp at this

end Singular


section Levi

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def levDiag (a : Fin n) (c : Kˣ) : Fin n → K :=
  fun i => if i = a then ((c⁻¹ ^ (n - 1) : Kˣ) : K) else (c : K)

theorem prod_levDiag (a : Fin n) (c : Kˣ) : ∏ i, levDiag a c i = 1 := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
  rw [Finset.prod_congr rfl fun i hi =>
      show levDiag a c i = (c : K) by simp [levDiag, Finset.ne_of_mem_erase hi],
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin]
  simp only [levDiag, ite_true]
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow,
    Units.val_one]

theorem levDiag_mul (a : Fin n) (c d : Kˣ) : levDiag a (c * d) = levDiag a c * levDiag a d := by
  ext i
  simp only [levDiag, Pi.mul_apply]
  split_ifs
  · rw [← Units.val_mul, ← mul_pow, mul_inv, mul_comm c⁻¹ d⁻¹]
  · rw [Units.val_mul]

@[expose] noncomputable def levTorusHom (a : Fin n) : Kˣ →* SpecialLinearGroup (Fin n) K where
  toFun c := ⟨diagonal (levDiag a c), by rw [det_diagonal, prod_levDiag]⟩
  map_one' := Subtype.ext (by
    change diagonal (levDiag a 1) = 1
    rw [← diagonal_one]
    congr 1
    ext i
    simp [levDiag])
  map_mul' c d := Subtype.ext (by
    change diagonal (levDiag a (c * d)) = diagonal (levDiag a c) * diagonal (levDiag a d)
    rw [diagonal_mul_diagonal, levDiag_mul]
    rfl)

theorem coe_levTorusHom (a : Fin n) (c : Kˣ) :
    ((levTorusHom a c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (levDiag a c) :=
  rfl

@[expose] noncomputable def levTorus (a : Fin n) : Subgroup (LinearFlag.projectiveSL n K) :=
  ((LinearFlag.proj n K).comp (levTorusHom a)).range

theorem proj_levTorusHom_mem (a : Fin n) (c : Kˣ) :
    LinearFlag.proj n K (levTorusHom a c) ∈ levTorus (K := K) a :=
  ⟨c, rfl⟩

theorem levDiag_ne (hn : 1 ≤ n) {a : Fin n} {c : Kˣ} (hc : c ^ n ≠ 1) {i : Fin n} (hi : i ≠ a) :
    levDiag a c a ≠ levDiag a c i := by
  simp only [levDiag, ite_true, hi, ite_false]
  intro h
  apply hc
  have h' : c⁻¹ ^ (n - 1) = c := Units.ext h
  calc c ^ n = c ^ (n - 1) * c := by rw [← pow_succ, Nat.sub_add_cancel hn]
    _ = c ^ (n - 1) * c⁻¹ ^ (n - 1) := by rw [h']
    _ = 1 := by rw [← mul_pow, mul_inv_cancel, one_pow]

theorem mul_eq_mul_and_blockDiag_of_proj_commute_lev (hn : 3 ≤ n) {a : Fin n} {c : Kˣ}
    (hc : c ^ n ≠ 1) {A : SpecialLinearGroup (Fin n) K}
    (hA : LinearFlag.proj n K A * LinearFlag.proj n K (levTorusHom a c) =
      LinearFlag.proj n K (levTorusHom a c) * LinearFlag.proj n K A) :
    A * levTorusHom a c = levTorusHom a c * A ∧
      ∀ i j, (i ∈ ({a} : Finset (Fin n)) ↔ j ∉ ({a} : Finset (Fin n))) →
        (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
  rw [← map_mul, ← map_mul] at hA
  obtain ⟨μ, hμ⟩ := exists_smul_of_proj_eq hA
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_levTorusHom] at hμ
  have hentry : ∀ i j, levDiag a c i * (A : Matrix (Fin n) (Fin n) K) i j =
      (μ : K) * ((A : Matrix (Fin n) (Fin n) K) i j * levDiag a c j) := fun i j => by
    have := congrFun (congrFun hμ i) j
    rwa [diagonal_mul, Matrix.smul_apply, mul_diagonal, smul_eq_mul] at this
  have hμ1 : μ = 1 := by
    by_contra hμ1
    have hμ1' : (μ : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hμ1 (Units.ext h)
    have hzero : ∀ i j, i ≠ a → j ≠ a → (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
      intro i j hi hj
      have := hentry i j
      simp only [levDiag, hi, hj, ite_false] at this
      have h2 : ((μ : K) - 1) * (c : K) * (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
        linear_combination -this
      exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero hμ1' c.ne_zero)
    obtain ⟨j₁, j₂, hj₁, hj₂, hj⟩ : ∃ j₁ j₂ : Fin n, j₁ ≠ a ∧ j₂ ≠ a ∧ j₁ ≠ j₂ := by
      have hcard : 2 ≤ ((Finset.univ : Finset (Fin n)).erase a).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨j₁, h₁, j₂, h₂, h⟩ := Finset.one_lt_card.1 hcard
      exact ⟨j₁, j₂, Finset.ne_of_mem_erase h₁, Finset.ne_of_mem_erase h₂, h⟩
    have hdet := det_eq_zero_of_cols (c := a) hj (fun i hi => hzero i j₁ hi hj₁)
      (fun i hi => hzero i j₂ hi hj₂)
    rw [A.2] at hdet
    exact one_ne_zero hdet
  subst hμ1
  have hcomm : A * levTorusHom a c = levTorusHom a c * A := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_levTorusHom, hμ,
      Units.val_one, one_smul]
  refine ⟨hcomm, fun i j hij => ?_⟩
  have h1 := hentry i j
  rw [Units.val_one, one_mul] at h1
  have hne : levDiag a c i ≠ levDiag a c j := by
    by_cases hi : i = a
    · have hj : j ≠ a := by
        intro hj
        simp [hi, hj] at hij
      rw [hi]
      exact levDiag_ne (by omega) hc hj
    · have hj : j = a := by
        by_contra hj
        simp [hi, hj] at hij
      rw [hj]
      exact (levDiag_ne (by omega) hc hi).symm
  have h2 : (levDiag a c i - levDiag a c j) * (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
    linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

end Levi

section LeviCommutator

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {n : ℕ}

theorem mem_singleton_iff_mem_range (a : Fin n) (i : Fin n) :
    i ∈ ({a} : Finset (Fin n)) ↔ i ∈ Set.range ![a] := by
  rw [Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨0, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    rfl

theorem commutator_mem_of_mem_centralizer_lev (hn : 3 ≤ n) {a : Fin n} {c : Kˣ} (hc : c ^ n ≠ 1)
    {A B : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ Subgroup.centralizer ({levTorusHom a c} : Set (SpecialLinearGroup (Fin n) K)))
    (hB : B ∈ Subgroup.centralizer ({levTorusHom a c} : Set (SpecialLinearGroup (Fin n) K))) :
    A * B * A⁻¹ * B⁻¹ ∈ blockSpecialLinear ({a} : Finset (Fin n))ᶜ := by
  have hdiag : ∀ C ∈ Subgroup.centralizer
      ({levTorusHom a c} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ i j, (i ∈ ({a} : Finset (Fin n)) ↔ j ∉ ({a} : Finset (Fin n))) →
        (C : Matrix (Fin n) (Fin n) K) i j = 0 := fun C hC => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hC
    refine (mul_eq_mul_and_blockDiag_of_proj_commute_lev hn hc ?_).2
    rw [← map_mul, ← map_mul, hC]
  refine commutator_agrees_one_compl (r := 1) (e := ![a]) (fun _ _ _ => Subsingleton.elim _ _)
    (mem_singleton_iff_mem_range a) hdiag (fun C _ D _ => ?_) hA hB
  ext i j
  fin_cases i
  fin_cases j
  simp only [mul_apply, Fin.sum_univ_one, submatrix_apply]
  exact mul_comm _ _

end LeviCommutator

section Quasisimple

variable {K : Type*} [Field K] [Finite K] {n : ℕ}

theorem isQuasisimple_specialLinearGroup_of_le {m : ℕ} (hm : 2 ≤ m)
    (h : 3 ≤ m ∨ 4 ≤ Nat.card K) : CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) K) := by
  have h' : 3 ≤ m ∨ ∃ s : Finset K, s.card = 4 := by
    rcases h with h | h
    · exact Or.inl h
    · right
      have := Fintype.ofFinite K
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
      exact ⟨s, hs⟩
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) hm h'
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) hm h'
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hc
  push Not at hc
  have : IsMulCommutative (ProjectiveSpecialLinearGroup (Fin m) K) := ⟨⟨hc⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (ProjectiveSpecialLinearGroup (Fin m) K) this

theorem isQuasisimple_blockSL {I : Finset (Fin n)} (hI : I.card < n) (h2 : 2 ≤ I.card)
    (h : 3 ≤ I.card ∨ 4 ≤ Nat.card K) : CFSG.IsQuasisimple (blockSL (K := K) I) := by
  obtain ⟨e⟩ := blockSL_mulEquiv (K := K) hI
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (isQuasisimple_specialLinearGroup_of_le h2 h)

end Quasisimple

section Layer

variable {G : Type*} [Group G]

theorem inSubgroup_layer_eq_of_commutator_mem {H D : Subgroup G} (hDH : D ≤ H)
    (hcomm : ∀ g ∈ H, ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ D) (hD : CFSG.IsQuasisimple D) :
    inSubgroup layer H = D := by
  set KD : Subgroup H := D.subgroupOf H with hKD
  have hnormal : KD.Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [hKD, Subgroup.mem_subgroupOf] at hm ⊢
    have h1 := hcomm g g.2 m m.2
    have e : ((g * m * g⁻¹ : H) : G) = (g : G) * m * (g : G)⁻¹ * (m : G)⁻¹ * m := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact mul_mem h1 hm
  have hq : CFSG.IsQuasisimple KD :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDH).symm hD
  have hsolv : Group.IsSolvable (H ⧸ KD) := by
    refine Group.isSolvable_of_comm fun x y => ?_
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hKD,
          Subgroup.mem_subgroupOf]
        have h := hcomm _ (inv_mem y.2) _ (inv_mem x.2)
        have e : (((x * y)⁻¹ * (y * x) : H) : G) =
            (y : G)⁻¹ * (x : G)⁻¹ * ((y : G)⁻¹)⁻¹ * ((x : G)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact h
  rw [inSubgroup, CFSG.RankThree.PartOne.KFU.layer_eq_of_normal hnormal hq hsolv,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hDH]

end Layer

section TorusQ1

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {n : ℕ} {a b : Fin n}

theorem eq_one_of_sq_eq_one [CharP K 2] {c : K} (h : c ^ 2 = 1) : c = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0 : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)

theorem eq_one_of_mem_blockSpecialLinear_pair_of_mem_scalars [CharP K 2] (hab : a ≠ b)
    {z : SpecialLinearGroup (Fin n) K} (hz : z ∈ blockSpecialLinear ({a, b} : Finset (Fin n)))
    (hs : z ∈ LinearFlag.scalars n K) : z = 1 := by
  obtain ⟨c, hcn, hc⟩ := LinearFlag.mem_scalars.1 hs
  have hc1 : (c : K) = 1 := by
    by_cases h : ∃ j, j ∉ ({a, b} : Finset (Fin n))
    · obtain ⟨j, hj⟩ := h
      have := hz j j (Or.inl hj)
      rw [hc, scalar_apply, diagonal_apply_eq, one_apply_eq] at this
      exact this
    · push Not at h
      have huniv : ({a, b} : Finset (Fin n)) = Finset.univ := Finset.eq_univ_of_forall h
      have hn2 : n = 2 := by
        have := congrArg Finset.card huniv
        rw [Finset.card_pair hab, Finset.card_univ, Fintype.card_fin] at this
        exact this.symm
      subst hn2
      exact eq_one_of_sq_eq_one (by rw [← Units.val_pow_eq_pow_val, hcn, Units.val_one])
  exact Subtype.ext (by rw [hc, hc1, map_one, Matrix.SpecialLinearGroup.coe_one])

theorem orderOf_proj_of_mem_blockSpecialLinear_pair [CharP K 2] (hab : a ≠ b)
    {y : SpecialLinearGroup (Fin n) K} (hy : y ∈ blockSpecialLinear ({a, b} : Finset (Fin n))) :
    orderOf (LinearFlag.proj n K y) = orderOf y := by
  refine orderOf_eq_orderOf_iff.2 fun k => ⟨fun h => ?_, fun h => by rw [← map_pow, h, map_one]⟩
  rw [← map_pow, LinearFlag.proj_eq_one_iff] at h
  exact eq_one_of_mem_blockSpecialLinear_pair_of_mem_scalars hab (pow_mem hy k) h

theorem exists_torusQ1 [CharP K 2] (hab : a ≠ b) :
    ∃ X : Subgroup (LinearFlag.projectiveSL n K), X ≤ rootSL2 a b ∧ IsCyclic X ∧
      Nat.card X = Nat.card K + 1 := by
  by_cases hfin : Finite K
  swap
  · refine ⟨⊥, bot_le, inferInstance, ?_⟩
    have := not_finite_iff_infinite.1 hfin
    rw [Subgroup.card_bot, Nat.card_eq_zero_of_infinite]
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  set e : Fin 2 ≃ ({a, b} : Finset (Fin n)) :=
    (finCongr (Finset.card_pair hab).symm).trans ({a, b} : Finset (Fin n)).equivFin.symm
  set y : SpecialLinearGroup (Fin n) K := blockEmbed {a, b} (reindexSpecialLinear e A) with hydef
  have hy : y ∈ blockSpecialLinear ({a, b} : Finset (Fin n)) := by
    rw [← range_blockEmbed]
    exact ⟨_, rfl⟩
  have hyo : orderOf y = Nat.card K + 1 := by
    rw [hydef, orderOf_injective _ (blockEmbed_injective _), MulEquiv.orderOf_eq, hA]
  refine ⟨Subgroup.zpowers (LinearFlag.proj n K y), ?_, inferInstance, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact proj_mem_blockSL hy
  · rw [Nat.card_zpowers, orderOf_proj_of_mem_blockSpecialLinear_pair hab hy, hyo]

theorem odd_natCard_add_one [Finite K] [CharP K 2] : Odd (Nat.card K + 1) := by
  obtain ⟨k, hk⟩ := CFSG.SeitzReduction.F4Pilot.two_dvd_natCard_of_charP_two (K := K)
  exact ⟨k, by omega⟩

theorem exists_lift_torusQ1 [Finite K] [CharP K 2] {X : Subgroup (LinearFlag.projectiveSL n K)}
    (hX : X ≤ rootSL2 a b) (hXc : Nat.card X = Nat.card K + 1) :
    ∃ x ∈ X, ∃ y : SpecialLinearGroup (Fin n) K,
      y ∈ blockSpecialLinear ({a, b} : Finset (Fin n)) ∧ LinearFlag.proj n K y = x ∧ x ≠ 1 ∧
        x ^ (Nat.card K + 1) = 1 ∧ y * y ≠ 1 := by
  have hne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨⟨x, hxX⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxm : x ^ (Nat.card K + 1) = 1 := by
    have : (⟨x, hxX⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
    rw [hXc] at this
    exact congrArg Subtype.val this
  obtain ⟨y, hy, rfl⟩ := mem_blockSL.1 (hX hxX)
  refine ⟨_, hxX, y, hy, rfl, hx1', hxm, fun hyy => hx1' ?_⟩
  have hsq : LinearFlag.proj n K y ^ 2 = 1 := by rw [sq, ← map_mul, hyy, map_one]
  have hd1 := orderOf_dvd_of_pow_eq_one hsq
  have hd2 := orderOf_dvd_of_pow_eq_one hxm
  have hodd := odd_natCard_add_one (K := K)
  have hcop : Nat.Coprime 2 (Nat.card K + 1) := Nat.coprime_two_left.2 hodd
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

theorem blockSL_compl_le_centralizer {X : Subgroup (LinearFlag.projectiveSL n K)}
    (hX : X ≤ rootSL2 a b) :
    blockSL (({a, b} : Finset (Fin n))ᶜ) ≤
      Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K)) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (commute_blockSL_of_disjoint disjoint_compl_left d hd x (hX hx)).symm.eq

theorem commutator_mem_blockSL_of_mem_centralizer_torusQ1 [Finite K] [CharP K 2] (hab : a ≠ b)
    {X : Subgroup (LinearFlag.projectiveSL n K)} (hX : X ≤ rootSL2 a b)
    (hXc : Nat.card X = Nat.card K + 1) {g h : LinearFlag.projectiveSL n K}
    (hg : g ∈ Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K)))
    (hh : h ∈ Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K))) :
    g * h * g⁻¹ * h⁻¹ ∈ blockSL (({a, b} : Finset (Fin n))ᶜ) := by
  obtain ⟨x, hxX, y, hy, rfl, -, hxm, hyy⟩ := exists_lift_torusQ1 hX hXc
  have hlift : ∀ g ∈ Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K)),
      ∃ A : SpecialLinearGroup (Fin n) K, LinearFlag.proj n K A = g ∧
        A ∈ Subgroup.centralizer ({y} : Set (SpecialLinearGroup (Fin n) K)) := fun g hg => by
    obtain ⟨A, rfl⟩ := LinearFlag.proj_surjective n K g
    refine ⟨A, rfl, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_eq_mul_of_proj_commute (Subgroup.mem_centralizer_iff.1 hg _ hxX).symm hxm
  obtain ⟨A, rfl, hA⟩ := hlift g hg
  obtain ⟨B, rfl, hB⟩ := hlift h hh
  have hmem : A * B * A⁻¹ * B⁻¹ ∈ blockSpecialLinear (({a, b} : Finset (Fin n))ᶜ) :=
    commutator_agrees_one_of_mem_centralizer hab hy hyy hA hB
  have := proj_mem_blockSL hmem
  simpa only [map_mul, map_inv] using this

theorem layer_centralizer_torusQ1_of_four_le [Finite K] [CharP K 2] (hn : 4 ≤ n)
    (hnq : 5 ≤ n ∨ 4 ≤ Nat.card K) (hab : a ≠ b) {X : Subgroup (LinearFlag.projectiveSL n K)}
    (hX : X ≤ rootSL2 a b) (hXc : Nat.card X = Nat.card K + 1) :
    inSubgroup layer (Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K))) =
      blockSL (({a, b} : Finset (Fin n))ᶜ) := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  refine inSubgroup_layer_eq_of_commutator_mem (blockSL_compl_le_centralizer hX)
    (fun g hg h hh => commutator_mem_blockSL_of_mem_centralizer_torusQ1 hab hX hXc hg hh)
    (isQuasisimple_blockSL (by omega) (by omega) ?_)
  rcases hnq with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

theorem layer_centralizer_torusQ1 [Finite K] [CharP K 2] (hn : 5 ≤ n) (hab : a ≠ b)
    {X : Subgroup (LinearFlag.projectiveSL n K)} (hX : X ≤ rootSL2 a b)
    (hXc : Nat.card X = Nat.card K + 1) :
    inSubgroup layer (Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K))) =
      blockSL (({a, b} : Finset (Fin n))ᶜ) :=
  layer_centralizer_torusQ1_of_four_le (by omega) (Or.inl hn) hab hX hXc

end TorusQ1

section LeviLayer

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {n : ℕ}

theorem blockSL_compl_le_centralizer_levTorus (a : Fin n) :
    blockSL (({a} : Finset (Fin n))ᶜ) ≤
      Subgroup.centralizer (levTorus (K := K) a : Set (LinearFlag.projectiveSL n K)) := by
  rintro _ ⟨B, hB, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨c, rfl⟩
  rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_levTorusHom]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hi : i = a
  · have h1 := hB i j (Or.inl (by simp [hi]))
    by_cases hij : i = j
    · subst hij
      ring
    · rw [h1, one_apply_ne hij, mul_zero, zero_mul]
  · by_cases hj : j = a
    · have h1 := hB i j (Or.inr (by simp [hj]))
      rw [h1, one_apply_ne (fun h : i = j => hi (h.trans hj)), mul_zero, zero_mul]
    · simp only [levDiag, hi, hj, ite_false]
      ring

theorem commutator_mem_blockSL_of_mem_centralizer_levTorus (hn : 3 ≤ n) {a : Fin n}
    (hc : ∃ c : Kˣ, c ^ n ≠ 1) {g h : LinearFlag.projectiveSL n K}
    (hg : g ∈ Subgroup.centralizer (levTorus (K := K) a : Set (LinearFlag.projectiveSL n K)))
    (hh : h ∈ Subgroup.centralizer (levTorus (K := K) a : Set (LinearFlag.projectiveSL n K))) :
    g * h * g⁻¹ * h⁻¹ ∈ blockSL (({a} : Finset (Fin n))ᶜ) := by
  obtain ⟨c, hc⟩ := hc
  have hlift : ∀ g ∈ Subgroup.centralizer
      (levTorus (K := K) a : Set (LinearFlag.projectiveSL n K)),
      ∃ A : SpecialLinearGroup (Fin n) K, LinearFlag.proj n K A = g ∧
        A ∈ Subgroup.centralizer ({levTorusHom a c} : Set (SpecialLinearGroup (Fin n) K)) :=
    fun g hg => by
      obtain ⟨A, rfl⟩ := LinearFlag.proj_surjective n K g
      refine ⟨A, rfl, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_eq_mul_and_blockDiag_of_proj_commute_lev hn hc
        (Subgroup.mem_centralizer_iff.1 hg _ (proj_levTorusHom_mem a c)).symm).1
  obtain ⟨A, rfl, hA⟩ := hlift g hg
  obtain ⟨B, rfl, hB⟩ := hlift h hh
  have := proj_mem_blockSL (commutator_mem_of_mem_centralizer_lev hn hc hA hB)
  simpa only [map_mul, map_inv] using this

theorem layer_centralizer_levTorus_of_four_le [Finite K] (hn : 4 ≤ n) (a : Fin n)
    (hc : ∃ c : Kˣ, c ^ n ≠ 1) :
    inSubgroup layer
        (Subgroup.centralizer (levTorus (K := K) a : Set (LinearFlag.projectiveSL n K))) =
      blockSL (({a} : Finset (Fin n))ᶜ) := by
  have hcard : (({a} : Finset (Fin n))ᶜ).card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  exact inSubgroup_layer_eq_of_commutator_mem (blockSL_compl_le_centralizer_levTorus a)
    (fun g hg h hh => commutator_mem_blockSL_of_mem_centralizer_levTorus (by omega) hc hg hh)
    (isQuasisimple_blockSL (by omega) (by omega) (Or.inl (by omega)))

theorem exists_pow_four_ne_one [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ∃ c : Kˣ, c ^ 4 ≠ 1 := by
  have h1 : 1 < Nat.card Kˣ := by
    rw [Nat.card_units]
    omega
  have := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨c, hc⟩ := exists_ne (1 : Kˣ)
  refine ⟨c, fun h4 => hc (Units.ext ?_)⟩
  have h4' : ((c : K) ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, ← Units.val_pow_eq_pow_val, h4, Units.val_one]
  rw [Units.val_one]
  exact eq_one_of_sq_eq_one (eq_one_of_sq_eq_one h4')

theorem layer_centralizer_levTorus [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) (a : Fin 4) :
    inSubgroup layer
        (Subgroup.centralizer (levTorus (K := K) a : Set (LinearFlag.projectiveSL 4 K))) =
      blockSL (({a} : Finset (Fin 4))ᶜ) :=
  layer_centralizer_levTorus_of_four_le le_rfl a (exists_pow_four_ne_one hq)

end LeviLayer

end CFSG.SeitzReduction.LinearPilot
