module

public import CFSG.Fischer.Classification.Orthogonal3.Forms

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open F3

@[expose] def diagF3Entry (m : ℕ) (δ : ZMod 3) (i : Fin m) : ZMod 3 :=
  if (i : ℕ) + 1 = m then δ else 1

@[expose] noncomputable def diagF3 (m : ℕ) (δ : ZMod 3) :
    LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3) :=
  Matrix.toBilin' (Matrix.diagonal (diagF3Entry m δ))

theorem diagF3_apply (m : ℕ) (δ : ZMod 3) (x y : Fin m → ZMod 3) :
    diagF3 m δ x y = ∑ i, diagF3Entry m δ i * x i * y i := by
  rw [diagF3, Matrix.toBilin'_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [Matrix.diagonal_apply_ne _ hji.symm,
    mul_zero, zero_mul]) (fun h => absurd (Finset.mem_univ i) h), Matrix.diagonal_apply_eq]
  ring

theorem diagF3Entry_ne_zero {m : ℕ} {δ : ZMod 3} (hδ : δ ≠ 0) (i : Fin m) :
    diagF3Entry m δ i ≠ 0 := by
  rw [diagF3Entry]
  split_ifs
  · exact hδ
  · exact one_ne_zero

theorem isF3Form_diagF3 {m : ℕ} {δ : ZMod 3} (hδ : δ ≠ 0) : IsF3Form (diagF3 m δ) := by
  refine ⟨fun x y => by
    simp only [diagF3_apply]
    exact Finset.sum_congr rfl fun i _ => by ring, fun x hx => funext fun j => ?_⟩
  have h := hx (Pi.single j 1)
  rw [diagF3_apply, Finset.sum_eq_single j (fun i _ hij => by
    rw [Pi.single_eq_of_ne hij, mul_zero]) (fun h => absurd (Finset.mem_univ j) h),
    Pi.single_eq_same, mul_one] at h
  exact (mul_eq_zero.1 h).resolve_left (diagF3Entry_ne_zero hδ j)

@[expose] noncomputable def I5Form : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) :=
  Matrix.toBilin' 1

theorem I5Form_apply (x y : Fin 5 → ZMod 3) : I5Form x y = ∑ i, x i * y i := by
  rw [I5Form, Matrix.toBilin'_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [Matrix.one_apply_ne hji.symm, mul_zero,
    zero_mul]) (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq, mul_one]

theorem diagF3_five_one : diagF3 5 1 = I5Form := by
  refine LinearMap.ext₂ fun x y => ?_
  rw [diagF3_apply, I5Form_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagF3Entry, ite_self, one_mul]

theorem isF3Form_I5Form : IsF3Form I5Form :=
  diagF3_five_one ▸ isF3Form_diagF3 one_ne_zero

namespace Beta

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem nondegOn_perpSub_orthonormal (hf : IsF3Form f) {k : ℕ} {w : Fin k → Fin m → ZMod 3}
    (hw : ∀ i j, f (w i) (w j) = if i = j then 1 else 0) :
    ∀ y ∈ perpSub f w, y ≠ 0 → ∃ y' ∈ perpSub f w, f y y' ≠ 0 := by
  refine nondegOn_of_proj hf (fun y => y - ∑ i, f y (w i) • w i)
    (fun y => mem_perpSub.2 fun j => ?_) fun x hx y => ?_
  · rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sum_left]
    simp only [LinearMap.BilinForm.smul_left, hw, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]
  · rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.sum_right]
    simp only [LinearMap.BilinForm.smul_right, mem_perpSub.1 hx, mul_zero,
      Finset.sum_const_zero, sub_zero]

theorem exists_orthonormalF3 (hf : IsF3Form f) :
    ∀ k, k < m → ∃ w : Fin k → Fin m → ZMod 3, ∀ i j, f (w i) (w j) = if i = j then 1 else 0
  | 0, _ => ⟨Fin.elim0, fun i => i.elim0⟩
  | k + 1, hk => by
    obtain ⟨w, hw⟩ := exists_orthonormalF3 hf k (by omega)
    obtain ⟨y, hyU, hyy⟩ := exists_mem_norm_eq hf (nondegOn_perpSub_orthonormal hf hw)
      (perpSub_twoDim hf (k := k) (by omega) w) (c := 1) one_ne_zero
    have hyw : ∀ i, f y (w i) = 0 := mem_perpSub.1 hyU
    have hwy : ∀ i, f (w i) y = 0 := fun i => by rw [hf.symm]; exact hyw i
    refine ⟨Fin.snoc w y, fun i j => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hyy]
      | cast j => simp [hyw, (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [hwy, (Fin.castSucc_lt_last i).ne]
      | cast j => simp [hw, Fin.castSucc_inj]

end Beta

theorem exists_linearEquiv_diagF3 {m : ℕ} (hm : 1 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f) :
    ∃ (δ : ZMod 3) (e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)), (δ = 1 ∨ δ = 2) ∧
      ∀ x y, f x y = diagF3 m δ (e x) (e y) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨w, hw⟩ := Beta.exists_orthonormalF3 hf n (by omega)
  obtain ⟨y, hy0, hyw⟩ := exists_ne_zero_perp (f := f) (Nat.lt_succ_self n) w
  have hwy : ∀ i, f (w i) y = 0 := fun i => by rw [hf.symm]; exact hyw i
  set W : Fin (n + 1) → Fin (n + 1) → ZMod 3 := Fin.snoc w y with hW
  set δ := f y y with hδ
  have hWW : ∀ i j, f (W i) (W j) = if i = j then diagF3Entry (n + 1) δ i else 0 := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [hW, diagF3Entry] using hδ.symm
      | cast j => simp [hW, hyw, (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [hW, hwy, (Fin.castSucc_lt_last i).ne]
      | cast j =>
        by_cases hij : i = j
        · subst hij
          simp [hW, hw, diagF3Entry, i.isLt.ne]
        · simp [hW, hw, hij, Fin.castSucc_inj]
  have hli : LinearIndependent (ZMod 3) W := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hcast : ∀ j : Fin n, g j.castSucc = 0 := fun j => by
      have := congrArg (fun x => f x (W j.castSucc)) hg
      simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left, hWW, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, LinearMap.BilinForm.zero_left]
        at this
      simpa [diagF3Entry, j.isLt.ne] using this
    have hlast : g (Fin.last n) = 0 := by
      rw [Fin.sum_univ_castSucc] at hg
      simp only [hcast, zero_smul, Finset.sum_const_zero, zero_add, hW, Fin.snoc_last] at hg
      exact (smul_eq_zero.1 hg).resolve_right hy0
    intro i
    induction i using Fin.lastCases with
    | last => exact hlast
    | cast j => exact hcast j
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ∀ i, b i = W i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hform : ∀ x y', f x y' = diagF3 (n + 1) δ (b.equivFun x) (b.equivFun y') := by
    intro x y'
    conv_lhs => rw [← b.sum_equivFun x, ← b.sum_equivFun y']
    simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.sum_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hb, hWW, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [diagF3_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hy0
    refine hf.nondeg y fun x => ?_
    have hyb : b.equivFun y = Pi.single (Fin.last n) 1 := by
      rw [← b.equivFun.apply_symm_apply (Pi.single (Fin.last n) 1),
        b.equivFun_symm_apply]
      congr 1
      rw [Finset.sum_eq_single (Fin.last n) (fun i _ hi => by
        rw [Pi.single_eq_of_ne hi, zero_smul]) (fun h => absurd (Finset.mem_univ _) h),
        Pi.single_eq_same, one_smul, hb, hW, Fin.snoc_last]
    rw [hform, hyb, diagF3_apply, Finset.sum_eq_single (Fin.last n) (fun i _ hi => by
      rw [Pi.single_eq_of_ne hi, mul_zero, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]
    simp [diagF3Entry, h0]
  refine ⟨δ, b.equivFun, ?_, hform⟩
  revert hδ0
  generalize δ = d
  revert d
  decide

end CFSG.Fischer.Classification
