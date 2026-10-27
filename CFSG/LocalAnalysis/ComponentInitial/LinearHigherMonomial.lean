module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.LinearAlgebra.Matrix.IsDiag

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem monomial_apply {M : Matrix (Fin n) (Fin n) K} {w : Equiv.Perm (Fin n)} {c : Fin n → K}
    (hM : ∀ j, M *ᵥ Pi.single j 1 = c j • Pi.single (w j) 1) (i j : Fin n) :
    M i j = if i = w j then c j else 0 := by
  have h := congrFun (hM j) i
  rw [mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at h
  rw [h]
  split_ifs <;> simp

theorem monomial_mul_single {M : Matrix (Fin n) (Fin n) K} {w : Equiv.Perm (Fin n)}
    {c : Fin n → K} (hc : ∀ j, c j ≠ 0) (hM : ∀ i j, M i j = if i = w j then c j else 0)
    (a b : Fin n) (t : K) :
    M * single a b t = single (w a) (w b) (c a * (c b)⁻¹ * t) * M := by
  ext i j
  by_cases hj : j = b
  · subst hj
    rw [mul_single_apply_same]
    by_cases hi : i = w a
    · subst hi
      rw [single_mul_apply_same, hM, hM, ite_eq_left rfl, ite_eq_left rfl]
      field_simp [hc j]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hi, hM, ite_eq_right hi, zero_mul]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hj]
    by_cases hi : i = w a
    · subst hi
      rw [single_mul_apply_same, hM, ite_eq_right (fun h => hj (w.injective h).symm), mul_zero]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hi]

theorem monomial_conj_transvection {M : SpecialLinearGroup (Fin n) K} {w : Equiv.Perm (Fin n)}
    {c : Fin n → Kˣ}
    (hM : ∀ j, (M : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 = (c j : K) • Pi.single (w j) 1)
    {a b : Fin n} (hab : a ≠ b) (t : K) :
    M * SpecialLinearGroup.transvection hab t * M⁻¹ =
      SpecialLinearGroup.transvection (w.injective.ne hab) ((c a : K) * (c b : K)⁻¹ * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    mul_one, one_mul]
  rw [monomial_mul_single (fun j => (c j).ne_zero) (monomial_apply hM)]

theorem transvection_mul_transvection_mul_transvection {a b : Fin n} (hab : a ≠ b) :
    ((1 : Matrix (Fin n) (Fin n) K) + single a b (-1)) * (1 + single b a 1) *
        (1 + single a b (-1)) =
      1 - single a a 1 - single b b 1 - single a b 1 + single b a 1 := by
  simp only [add_mul, mul_add, one_mul, mul_one, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ (Ne.symm hab), add_zero]
  ext r s
  simp only [Matrix.add_apply, Matrix.sub_apply, single_apply, one_apply]
  split_ifs <;> simp_all [sub_eq_add_neg]

theorem reflectionMatrix_eq_single (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    reflectionMatrix n K i =
      1 - single (⟨i - 1, by omega⟩ : Fin n) ⟨i - 1, by omega⟩ 1 - single ⟨i, hin⟩ ⟨i, hin⟩ 1 -
        single ⟨i - 1, by omega⟩ ⟨i, hin⟩ 1 + single ⟨i, hin⟩ ⟨i - 1, by omega⟩ 1 := by
  ext r s
  simp only [reflectionMatrix, of_apply, Matrix.add_apply, Matrix.sub_apply, single_apply,
    one_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem monomial_root_transport :
    (∀ (M : SpecialLinearGroup (Fin n) K) (w : Equiv.Perm (Fin n)) (c : Fin n → Kˣ),
      (∀ j, (M : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 = (c j : K) • Pi.single (w j) 1) →
      ∀ (a b : Fin n) (hab : a ≠ b),
        (∀ t : K, M * SpecialLinearGroup.transvection hab t * M⁻¹ =
          SpecialLinearGroup.transvection (w.injective.ne hab) ((c a : K) * (c b : K)⁻¹ * t)) ∧
        Set.range (fun t : K => M * SpecialLinearGroup.transvection hab t * M⁻¹) =
          Set.range (SpecialLinearGroup.transvection (w.injective.ne hab) : K → _)) ∧
    (∀ (M M' : SpecialLinearGroup (Fin n) K) (w : Equiv.Perm (Fin n)) (c c' : Fin n → Kˣ),
      (∀ j, (M : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 = (c j : K) • Pi.single (w j) 1) →
      (∀ j, (M' : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 = (c' j : K) • Pi.single (w j) 1) →
      ∃ D ∈ upperTriangular n K, Matrix.IsDiag (D : Matrix (Fin n) (Fin n) K) ∧ M = M' * D) ∧
    (∀ (i : ℕ) (hi : 1 ≤ i) (hin : i < n),
      reflection n K i hi hin =
        SpecialLinearGroup.transvection (i := ⟨i - 1, by omega⟩) (j := ⟨i, hin⟩)
            (fun h => by simp [Fin.ext_iff] at h; omega) (-1) *
          SpecialLinearGroup.transvection (i := ⟨i, hin⟩) (j := ⟨i - 1, by omega⟩)
            (fun h => by simp [Fin.ext_iff] at h; omega) 1 *
          SpecialLinearGroup.transvection (i := ⟨i - 1, by omega⟩) (j := ⟨i, hin⟩)
            (fun h => by simp [Fin.ext_iff] at h; omega) (-1)) := by
  refine ⟨fun M w c hM a b hab => ⟨fun t => monomial_conj_transvection hM hab t, ?_⟩,
    fun M M' w c c' hM hM' => ?_, fun i hi hin => ?_⟩
  ·
    ext g
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, (monomial_conj_transvection hM hab t).symm⟩
    · rintro ⟨s, rfl⟩
      refine ⟨(c b : K) * (c a : K)⁻¹ * s, ?_⟩
      change M * SpecialLinearGroup.transvection hab _ * M⁻¹ = _
      rw [monomial_conj_transvection hM hab]
      congr 1
      field_simp [(c a).ne_zero, (c b).ne_zero]
  ·
    set D := M'⁻¹ * M with hD
    have hinj : ∀ v v' : Fin n → K,
        (M' : Matrix (Fin n) (Fin n) K) *ᵥ v = (M' : Matrix (Fin n) (Fin n) K) *ᵥ v' → v = v' := by
      intro v v' h
      have h' := congrArg (fun x => ((M'⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ x) h
      simp only [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
        SpecialLinearGroup.coe_one, one_mulVec] at h'
      exact h'
    have hMD : (M' : Matrix (Fin n) (Fin n) K) * (D : Matrix (Fin n) (Fin n) K) =
        (M : Matrix (Fin n) (Fin n) K) := by
      rw [← SpecialLinearGroup.coe_mul, hD, mul_inv_cancel_left]
    have hcol : ∀ j, (D : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 =
        ((c j : K) * (c' j : K)⁻¹) • Pi.single j 1 := by
      intro j
      apply hinj
      rw [mulVec_mulVec, hMD, hM, mulVec_smul, hM', smul_smul,
        inv_mul_cancel_right₀ (c' j).ne_zero]
    have hentry : ∀ i j, (D : Matrix (Fin n) (Fin n) K) i j =
        if i = j then (c j : K) * (c' j : K)⁻¹ else 0 := fun i j => by
      have h := congrFun (hcol j) i
      rw [mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at h
      rw [h]
      split_ifs <;> simp
    refine ⟨D, fun i j hij => ?_, fun i j hij => ?_, ?_⟩
    · rw [hentry, ite_eq_right (ne_of_gt hij)]
    · change (D : Matrix (Fin n) (Fin n) K) i j = 0
      rw [hentry, ite_eq_right hij]
    · rw [hD, mul_inv_cancel_left]
  ·
    apply Subtype.ext
    simp only [coe_reflection, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
    rw [reflectionMatrix_eq_single i hi hin, transvection_mul_transvection_mul_transvection]
    intro h
    simp [Fin.ext_iff] at h
    omega

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
