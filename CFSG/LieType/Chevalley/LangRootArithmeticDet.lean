module

public import CFSG.Blueprint.ChevalleyInfinitesimals

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Polynomial

@[expose] def laplaceDet : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, _ => 1
  | n + 1, A => ((List.finRange (n + 1)).map fun j =>
      if A 0 j = 0 then 0
      else (-1) ^ (j : ℕ) * A 0 j * laplaceDet n (A.submatrix Fin.succ j.succAbove)).sum

theorem laplaceDet_eq_det : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), laplaceDet n A = A.det
  | 0, A => by
    rw [Matrix.det_fin_zero]
    rfl
  | n + 1, A => by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_def, laplaceDet.eq_2]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    split_ifs with h
    · rw [h, mul_zero, zero_mul]
    · rw [laplaceDet_eq_det n]

theorem det_cartan_G2 : Tag.G2.cartan.det = 1 := by
  rw [← laplaceDet_eq_det]
  decide +kernel

theorem det_cartan_F4 : Tag.F4.cartan.det = 1 := by
  rw [← laplaceDet_eq_det]
  decide +kernel

theorem det_cartan_D4 : Tag.D4.cartan.det = 4 := by
  rw [← laplaceDet_eq_det]
  decide +kernel

theorem det_cartan_E6 : Tag.E6.cartan.det = 3 := by
  rw [← laplaceDet_eq_det]
  decide +kernel

theorem det_cartan_E7 : Tag.E7.cartan.det = 2 := by
  rw [← laplaceDet_eq_det]
  decide +kernel

theorem det_cartan_E8 : Tag.E8.cartan.det = 1 := by
  rw [← laplaceDet_eq_det]
  decide +kernel

@[expose] def stringsLeTwo (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k => (List.finRange τ.rank).all fun i =>
    decide (τ.stringData.up k i ≤ 2 ∧ τ.stringData.down k i ≤ 2)

theorem stringsLeTwo_eq_true {τ : Tag} (hτ : τ ≠ .G2) : stringsLeTwo τ = true := by
  cases τ
  · exact absurd rfl hτ
  all_goals decide +kernel

theorem not_isRoot_add_three_smul
    {τ : Tag} (hτ : τ ≠ .G2) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {i : Fin τ.rank} (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    ¬IsRoot τ (α + (3 : ℤ) • Pi.single i 1) ∧ ¬IsRoot τ (α - (3 : ℤ) • Pi.single i 1) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  have h := stringsLeTwo_eq_true hτ
  simp only [stringsLeTwo, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    decide_eq_true_eq] at h
  obtain ⟨hu, hd⟩ := h k hk i
  have hs := (StringData.isRoot_root_add_iff τ.rootCertificate_check τ.stringData_check hk i
    h₁ h₂).2
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · have := ((hs 3).1 hr).2
    omega
  · rw [sub_eq_add_neg, ← neg_smul] at hr
    have := ((hs (-3)).1 hr).1
    omega

variable {R : Type*} [CommRing R]

theorem rootVec_eq_single_of_isRoot' {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 := by
  unfold rootVec
  exact dite_eq_left hβ

theorem rootVec_eq_zero_of_not_isRoot' {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : ¬IsRoot τ β) :
    rootVec τ R β = 0 := by
  unfold rootVec
  exact dite_eq_right hβ

theorem xCoeff_three_eq_zero
    {τ : Tag} (hτ : τ ≠ .G2) (i : Fin τ.rank) :
    xCoeff τ R i 3 = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rcases b with j | ⟨α, hα⟩
  · exact (xCoeff_hVec i j 3).trans (by simp)
  · rw [← rootVec_eq_single_of_isRoot' hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xCoeff_rootVec_single]
      simp
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single]
      simp
    rw [xCoeff_rootVec_of_ne i 3 hα h₁ h₂, Nat.cast_ofNat,
      rootVec_eq_zero_of_not_isRoot' (not_isRoot_add_three_smul hτ hα h₁ h₂).1, smul_zero]

theorem yCoeff_three_eq_zero
    {τ : Tag} (hτ : τ ≠ .G2) (i : Fin τ.rank) :
    yCoeff τ R i 3 = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rcases b with j | ⟨α, hα⟩
  · exact (yCoeff_hVec i j 3).trans (by simp)
  · rw [← rootVec_eq_single_of_isRoot' hα]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yCoeff_rootVec_neg_single]
      simp
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yCoeff_rootVec_single]
      simp
    rw [yCoeff_rootVec_of_ne i 3 hα h₁ h₂, Nat.cast_ofNat,
      rootVec_eq_zero_of_not_isRoot' (not_isRoot_add_three_smul hτ hα h₁ h₂).2, smul_zero]

@[expose] def entryDegreeBound (τ : Tag) : ℕ :=
  if τ = .G2 then 3 else 2

theorem natDegree_sum_C_mul_X_pow_le (d : ℕ) (a : ℕ → R) :
    (∑ k ∈ Finset.range (d + 1), C (a k) * X ^ k).natDegree ≤ d :=
  natDegree_sum_le_of_forall_le _ _ fun _ hk =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

theorem eval_sum_C_mul_X_pow (d : ℕ) (a : ℕ → R) (c : R) :
    (∑ k ∈ Finset.range (d + 1), C (a k) * X ^ k).eval c =
      ∑ k ∈ Finset.range (d + 1), c ^ k * a k := by
  rw [eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

theorem xOp_eq_sum_xCoeff_entryDegreeBound
    (τ : Tag) (i : Fin τ.rank) (c : R) :
    xOp τ R i c = ∑ k ∈ Finset.range (entryDegreeBound τ + 1), c ^ k • xCoeff τ R i k := by
  rw [xOp_eq_sum_xCoeff]
  by_cases hτ : τ = .G2
  · simp only [entryDegreeBound, hτ, ↓reduceIte]
  · simp only [entryDegreeBound, hτ, ↓reduceIte]
    rw [Finset.sum_range_succ _ 3, xCoeff_three_eq_zero hτ, smul_zero, add_zero]

theorem yOp_eq_sum_yCoeff_entryDegreeBound
    (τ : Tag) (i : Fin τ.rank) (c : R) :
    yOp τ R i c = ∑ k ∈ Finset.range (entryDegreeBound τ + 1), c ^ k • yCoeff τ R i k := by
  rw [yOp_eq_sum_yCoeff]
  by_cases hτ : τ = .G2
  · simp only [entryDegreeBound, hτ, ↓reduceIte]
  · simp only [entryDegreeBound, hτ, ↓reduceIte]
    rw [Finset.sum_range_succ _ 3, yCoeff_three_eq_zero hτ, smul_zero, add_zero]

variable (R) in
theorem exists_entry_polynomial
    (τ : Tag) (i : Fin τ.rank) (a b : Label τ) :
    ∃ p q : R[X], p.natDegree ≤ entryDegreeBound τ ∧ q.natDegree ≤ entryDegreeBound τ ∧
      ∀ c : R, xOp τ R i c (Finsupp.single b 1) a = p.eval c ∧
        yOp τ R i c (Finsupp.single b 1) a = q.eval c := by
  refine ⟨∑ k ∈ Finset.range (entryDegreeBound τ + 1),
      C (xCoeff τ R i k (Finsupp.single b 1) a) * X ^ k,
    ∑ k ∈ Finset.range (entryDegreeBound τ + 1),
      C (yCoeff τ R i k (Finsupp.single b 1) a) * X ^ k,
    natDegree_sum_C_mul_X_pow_le _ _, natDegree_sum_C_mul_X_pow_le _ _, fun c => ⟨?_, ?_⟩⟩
  · rw [eval_sum_C_mul_X_pow, xOp_eq_sum_xCoeff_entryDegreeBound, LinearMap.sum_apply,
      Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  · rw [eval_sum_C_mul_X_pow, yOp_eq_sum_yCoeff_entryDegreeBound, LinearMap.sum_apply,
      Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]

end CFSG.LieType.Chevalley
