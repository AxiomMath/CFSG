module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNormalForm

public section

namespace CFSG.LieType.SpecialLinear

open Matrix

open CFSG.SeitzReduction.LinearPilot

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_permMatrix_of_charTwo [CharP K 2] (σ : Equiv.Perm ι) : (σ.permMatrix K).det = 1 := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;>
    simp [CharTwo.neg_eq]

private theorem adjugate_eq_inv_of_det_eq_one {M : Matrix ι ι K} (hM : M.det = 1) :
    M.adjugate = M⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [Matrix.mul_adjugate, hM, one_smul]

theorem permMatrix_mulVec_single (σ : Equiv.Perm ι) (i : ι) :
    σ.permMatrix K *ᵥ (Pi.single i (1 : K) : ι → K) = Pi.single (σ.symm i) (1 : K) := by
  rw [Matrix.permMatrix_mulVec]
  funext j
  rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : σ j = i
  · rw [if_pos h, if_pos ((Equiv.apply_eq_iff_eq_symm_apply σ).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((Equiv.apply_eq_iff_eq_symm_apply σ).mpr h'))]

theorem det_one_add_nilOf {k : ℕ} {u w : Fin k → ι} (huw : ∀ a b, u a ≠ w b) :
    (1 + nilOf K u w).det = 1 := by
  classical
  set p : ι → Prop := fun i => ∃ a, w a = i with hp
  have hzero : ∀ i, p i → ∀ j, ¬ p j → (1 + nilOf K u w) i j = 0 := by
    intro i hi j hj
    rw [Matrix.add_apply, Matrix.one_apply, nilOf_apply]
    have hij : i ≠ j := fun h => hj (by rw [← h]; exact hi)
    rw [if_neg hij, zero_add]
    exact if_neg (by rintro ⟨a, -, hb⟩; exact hj ⟨a, hb⟩)
  rw [Matrix.twoBlockTriangular_det' (1 + nilOf K u w) p hzero]
  have h1 : Matrix.toSquareBlockProp (1 + nilOf K u w) p = 1 := by
    ext x y
    have hN : nilOf K u w (x : ι) (y : ι) = 0 := by
      rw [nilOf_apply]
      refine if_neg ?_
      rintro ⟨a, ha, -⟩
      obtain ⟨a0, ha0⟩ := x.2
      exact huw a a0 (ha.trans ha0.symm)
    rw [Matrix.toSquareBlockProp_def, Matrix.of_apply, Matrix.add_apply, hN, add_zero]
    by_cases hxy : x = y
    · rw [hxy, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hxy, Matrix.one_apply_ne fun h => hxy (Subtype.ext h)]
  have h2 : Matrix.toSquareBlockProp (1 + nilOf K u w) (fun i => ¬ p i) = 1 := by
    ext x y
    have hN : nilOf K u w (x : ι) (y : ι) = 0 := by
      rw [nilOf_apply]
      exact if_neg (by rintro ⟨a, -, hb⟩; exact y.2 ⟨a, hb⟩)
    rw [Matrix.toSquareBlockProp_def, Matrix.of_apply, Matrix.add_apply, hN, add_zero]
    by_cases hxy : x = y
    · rw [hxy, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hxy, Matrix.one_apply_ne fun h => hxy (Subtype.ext h)]
  rw [h1, h2]
  simp

omit [Fintype ι] [DecidableEq ι] in
private theorem add_self_eq_zero_vec [CharP K 2] (x : ι → K) : x + x = 0 := by
  funext i
  rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]

omit [Fintype ι] [DecidableEq ι] in
private theorem add_add_self_eq [CharP K 2] (x y : ι → K) : x + (x + y) = y := by
  rw [← add_assoc, add_self_eq_zero_vec, zero_add]

omit [Fintype ι] [DecidableEq ι] in
private theorem add_add_self_eq' [CharP K 2] (x y : ι → K) : (x + y) + x = y := by
  rw [add_assoc, add_comm y x, ← add_assoc, add_self_eq_zero_vec, zero_add]

omit [Fintype ι] [DecidableEq ι] in
private theorem add_add_comm_eq [CharP K 2] (x y : ι → K) : x + (y + x) = y := by
  rw [add_comm x (y + x), add_assoc, add_self_eq_zero_vec, add_zero]

theorem nilOf_mulVec_single_w {k : ℕ} {u w : Fin k → ι} (hw : Function.Injective w)
    (b : Fin k) :
    nilOf K u w *ᵥ (Pi.single (w b) (1 : K) : ι → K) = Pi.single (u b) (1 : K) := by
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, nilOf_apply, Pi.single_apply]
  by_cases h : ∃ a, u a = i ∧ w a = w b
  · obtain ⟨a, ha, hwab⟩ := h
    have hab : a = b := hw hwab
    have hiu : i = u b := by rw [← hab]; exact ha.symm
    rw [if_pos ⟨a, ha, hwab⟩, if_pos hiu]
  · rw [if_neg h, if_neg]
    intro hi
    exact h ⟨b, hi.symm, rfl⟩

theorem nilOf_mulVec_single_u {k : ℕ} {u w : Fin k → ι} (huw : ∀ a b, u a ≠ w b)
    (b : Fin k) :
    nilOf K u w *ᵥ (Pi.single (u b) (1 : K) : ι → K) = 0 := by
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, nilOf_apply, Pi.zero_apply]
  exact if_neg (by rintro ⟨a, -, hb⟩; exact huw b a hb.symm)

theorem nilOf_mulVec_single_of_forall_ne {k : ℕ} {u w : Fin k → ι} (j : ι)
    (hj : ∀ a, w a ≠ j) :
    nilOf K u w *ᵥ (Pi.single j (1 : K) : ι → K) = 0 := by
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, nilOf_apply, Pi.zero_apply]
  exact if_neg (by rintro ⟨a, -, hb⟩; exact hj a hb)

theorem one_add_nilOf_mulVec_single_u {k : ℕ} {u w : Fin k → ι}
    (huw : ∀ a b, u a ≠ w b) (b : Fin k) :
    (1 + nilOf K u w) *ᵥ (Pi.single (u b) (1 : K) : ι → K) =
      Pi.single (u b) (1 : K) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, nilOf_mulVec_single_u huw, add_zero]

theorem one_add_nilOf_mulVec_single_w {k : ℕ} {u w : Fin k → ι} (hw : Function.Injective w)
    (b : Fin k) :
    (1 + nilOf K u w) *ᵥ (Pi.single (w b) (1 : K) : ι → K) =
      (Pi.single (w b) (1 : K) : ι → K) + Pi.single (u b) (1 : K) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, nilOf_mulVec_single_w hw]

theorem one_add_nilOf_mulVec_single_of_forall_ne {k : ℕ} {u w : Fin k → ι} (j : ι)
    (hj : ∀ a, w a ≠ j) :
    (1 + nilOf K u w) *ᵥ (Pi.single j (1 : K) : ι → K) = Pi.single j (1 : K) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, nilOf_mulVec_single_of_forall_ne j hj, add_zero]

theorem one_add_nilOf_mulVec_single_add_u_w [CharP K 2] {k : ℕ} {u w : Fin k → ι}
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (b : Fin k) :
    (1 + nilOf K u w) *ᵥ
        ((Pi.single (u b) (1 : K) : ι → K) + Pi.single (w b) (1 : K)) =
      Pi.single (w b) (1 : K) := by
  rw [Matrix.mulVec_add, one_add_nilOf_mulVec_single_u huw,
    one_add_nilOf_mulVec_single_w hw, add_add_comm_eq]

variable (K) in
noncomputable def conjMat {k : ℕ} (u w : Fin k → ι) : Matrix ι ι K :=
  Matrix.of fun i j =>
    if ((i = j ∧ ¬ ∃ a, w a = i) ∨ (∃ a, w a = i ∧ u a = j)) ∨
        (∃ a, u a = i ∧ w a = j) then 1 else 0

omit [Fintype ι] in
theorem conjMat_apply_of_forall_ne_left {k : ℕ} {u w : Fin k → ι} (i : ι)
    (hu : ∀ a, u a ≠ i) (hw : ∀ a, w a ≠ i) (j : ι) :
    conjMat K u w i j = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · rw [hij] at hu hw ⊢
    rw [conjMat, Matrix.of_apply,
      if_pos (Or.inl (Or.inl ⟨rfl, fun ⟨a, ha⟩ => hw a ha⟩)), if_pos rfl]
  · have hcond : ¬ (((i = j ∧ ¬ ∃ a, w a = i) ∨ (∃ a, w a = i ∧ u a = j)) ∨
        (∃ a, u a = i ∧ w a = j)) := by
      rintro ((⟨h, -⟩ | ⟨a, ha, -⟩) | ⟨a, ha, -⟩)
      · exact hij h
      · exact hw a ha
      · exact hu a ha
    rw [conjMat, Matrix.of_apply, if_neg hcond, if_neg hij]

omit [Fintype ι] in
theorem conjMat_apply_of_forall_ne_right {k : ℕ} {u w : Fin k → ι} (j : ι)
    (hu : ∀ a, u a ≠ j) (hw : ∀ a, w a ≠ j) (i : ι) :
    conjMat K u w i j = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · rw [hij]
    exact conjMat_apply_of_forall_ne_left j hu hw j
  · have hcond : ¬ (((i = j ∧ ¬ ∃ a, w a = i) ∨ (∃ a, w a = i ∧ u a = j)) ∨
        (∃ a, u a = i ∧ w a = j)) := by
      rintro ((⟨h, -⟩ | ⟨a, -, ha⟩) | ⟨a, -, ha⟩)
      · exact hij h
      · exact hu a ha
      · exact hw a ha
    rw [conjMat, Matrix.of_apply, if_neg hcond, if_neg hij]

omit [Fintype ι] in
theorem conjMat_apply_u {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (i : ι) (a : Fin k) :
    conjMat K u w i (u a) =
      (if i = u a then 1 else 0) + (if i = w a then 1 else 0) := by
  by_cases hiu : ∃ b, u b = i
  · obtain ⟨b, rfl⟩ := hiu
    by_cases hba : b = a
    · rw [hba]
      rw [conjMat, Matrix.of_apply,
        if_pos (Or.inl (Or.inl ⟨rfl, fun ⟨c, hc⟩ => huw a c hc.symm⟩))]
      simp [huw a a]
    · have hA : ¬ (u b = u a) := fun h => hba (hu h)
      have hB : ¬ (∃ c, w c = u b ∧ u c = u a) := by
        rintro ⟨c, hc, -⟩
        exact huw b c hc.symm
      have hC : ¬ (∃ c, u c = u b ∧ w c = u a) := by
        rintro ⟨c, hc1, hc2⟩
        exact huw a b (by simpa [hu hc1] using hc2.symm)
      have hcond : ¬ (((u b = u a ∧ ¬ ∃ c, w c = u b) ∨
          (∃ c, w c = u b ∧ u c = u a)) ∨ (∃ c, u c = u b ∧ w c = u a)) := by
        rintro ((⟨h, -⟩ | hB') | hC')
        · exact hA h
        · exact hB hB'
        · exact hC hC'
      rw [conjMat, Matrix.of_apply, if_neg hcond, if_neg hA, if_neg (huw b a)]
      simp
  · by_cases hiw : ∃ b, w b = i
    · obtain ⟨b, rfl⟩ := hiw
      by_cases hba : b = a
      · rw [hba]
        have hwu : w a ≠ u a := fun h => huw a a h.symm
        rw [conjMat, Matrix.of_apply, if_pos (Or.inl (Or.inr ⟨a, rfl, rfl⟩))]
        simp [hwu]
      · have hA : ¬ (w b = u a) := fun h => huw a b h.symm
        have hB : ¬ (∃ c, w c = w b ∧ u c = u a) := by
          rintro ⟨c, hc1, hc2⟩
          exact hba (hu (by simpa [hw hc1] using hc2))
        have hC : ¬ (∃ c, u c = w b ∧ w c = u a) := by
          rintro ⟨c, hc, -⟩
          exact huw c b hc
        have hcond : ¬ (((w b = u a ∧ ¬ ∃ c, w c = w b) ∨
            (∃ c, w c = w b ∧ u c = u a)) ∨ (∃ c, u c = w b ∧ w c = u a)) := by
          rintro ((⟨h, -⟩ | hB') | hC')
          · exact hA h
          · exact hB hB'
          · exact hC hC'
        rw [conjMat, Matrix.of_apply, if_neg hcond, if_neg hA,
          if_neg (fun h => hba (hw h))]
        simp
    · have h1 : i ≠ u a := fun h => hiu ⟨a, h.symm⟩
      have h2 : i ≠ w a := fun h => hiw ⟨a, h.symm⟩
      rw [conjMat_apply_of_forall_ne_left i (fun b h => hiu ⟨b, h⟩)
        (fun b h => hiw ⟨b, h⟩)]
      simp [h1, h2]

omit [Fintype ι] in
theorem conjMat_apply_w {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (i : ι) (a : Fin k) :
    conjMat K u w i (w a) = if i = u a then 1 else 0 := by
  by_cases hiu : ∃ b, u b = i
  · obtain ⟨b, rfl⟩ := hiu
    by_cases hba : b = a
    · rw [hba]
      rw [conjMat, Matrix.of_apply, if_pos (Or.inr ⟨a, rfl, rfl⟩)]
      simp
    · have hA : ¬ (u b = w a) := huw b a
      have hB : ¬ (∃ c, w c = u b ∧ u c = w a) := by
        rintro ⟨c, hc, -⟩
        exact huw b c hc.symm
      have hC : ¬ (∃ c, u c = u b ∧ w c = w a) := by
        rintro ⟨c, hc1, hc2⟩
        exact hba (hw (by simpa [hu hc1] using hc2))
      have hcond : ¬ (((u b = w a ∧ ¬ ∃ c, w c = u b) ∨
          (∃ c, w c = u b ∧ u c = w a)) ∨ (∃ c, u c = u b ∧ w c = w a)) := by
        rintro ((⟨h, -⟩ | hB') | hC')
        · exact hA h
        · exact hB hB'
        · exact hC hC'
      rw [conjMat, Matrix.of_apply, if_neg hcond, if_neg (fun h => hba (hu h))]
  · by_cases hiw : ∃ b, w b = i
    · obtain ⟨b, rfl⟩ := hiw
      have hA : ¬ (w b = w a ∧ ¬ ∃ c, w c = w b) :=
        fun h => h.2 ⟨b, rfl⟩
      have hB : ¬ (∃ c, w c = w b ∧ u c = w a) := by
        rintro ⟨c, -, hc⟩
        exact huw c a hc
      have hC : ¬ (∃ c, u c = w b ∧ w c = w a) := by
        rintro ⟨c, hc, -⟩
        exact huw c b hc
      have hcond : ¬ (((w b = w a ∧ ¬ ∃ c, w c = w b) ∨
          (∃ c, w c = w b ∧ u c = w a)) ∨ (∃ c, u c = w b ∧ w c = w a)) := by
        rintro ((hA' | hB') | hC')
        · exact hA hA'
        · exact hB hB'
        · exact hC hC'
      rw [conjMat, Matrix.of_apply, if_neg hcond,
        if_neg (fun h : w b = u a => huw a b h.symm)]
    · have h1 : i ≠ u a := fun h => hiu ⟨a, h.symm⟩
      have h2 : i ≠ w a := fun h => hiw ⟨a, h.symm⟩
      rw [conjMat_apply_of_forall_ne_left i (fun b h => hiu ⟨b, h⟩)
        (fun b h => hiw ⟨b, h⟩)]
      simp [h1, h2]

theorem conjMat_mulVec_single_u {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (a : Fin k) :
    conjMat K u w *ᵥ (Pi.single (u a) (1 : K) : ι → K) =
      (Pi.single (u a) (1 : K) : ι → K) + Pi.single (w a) (1 : K) := by
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, conjMat_apply_u hu hw huw i a]
  simp [Pi.add_apply, Pi.single_apply]

theorem conjMat_mulVec_single_w {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (a : Fin k) :
    conjMat K u w *ᵥ (Pi.single (w a) (1 : K) : ι → K) = Pi.single (u a) (1 : K) := by
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, conjMat_apply_w hu hw huw i a]
  simp [Pi.single_apply]

theorem conjMat_mulVec_single_of_forall_ne {k : ℕ} {u w : Fin k → ι}
    (j : ι) (hju : ∀ a, u a ≠ j) (hjw : ∀ a, w a ≠ j) :
    conjMat K u w *ᵥ (Pi.single j (1 : K) : ι → K) = Pi.single j (1 : K) := by
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, conjMat_apply_of_forall_ne_right j hju hjw i]
  simp [Pi.single_apply]

theorem conjMat_mulVec_single_add_w_u [CharP K 2] {k : ℕ} {u w : Fin k → ι}
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b)
    (a : Fin k) :
    conjMat K u w *ᵥ ((Pi.single (w a) (1 : K) : ι → K) + Pi.single (u a) (1 : K)) =
      Pi.single (w a) (1 : K) := by
  rw [Matrix.mulVec_add, conjMat_mulVec_single_w hu hw huw,
    conjMat_mulVec_single_u hu hw huw, add_add_self_eq]

theorem conjMat_swap_mulVec_single_u {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (a : Fin k) :
    conjMat K w u *ᵥ (Pi.single (u a) (1 : K) : ι → K) = Pi.single (w a) (1 : K) :=
  conjMat_mulVec_single_w (K := K) (u := w) (w := u) hw hu (fun a b => (huw b a).symm) a

theorem conjMat_swap_mulVec_single_w {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (a : Fin k) :
    conjMat K w u *ᵥ (Pi.single (w a) (1 : K) : ι → K) =
      (Pi.single (u a) (1 : K) : ι → K) + Pi.single (w a) (1 : K) := by
  have h := conjMat_mulVec_single_u (K := K) (u := w) (w := u) hw hu
    (fun a b => (huw b a).symm) a
  rw [add_comm] at h
  exact h

theorem conjMat_swap_mulVec_single_of_forall_ne {k : ℕ} {u w : Fin k → ι}
    (j : ι) (hju : ∀ a, u a ≠ j) (hjw : ∀ a, w a ≠ j) :
    conjMat K w u *ᵥ (Pi.single j (1 : K) : ι → K) = Pi.single j (1 : K) :=
  conjMat_mulVec_single_of_forall_ne (K := K) (u := w) (w := u)
    j (fun a h => hjw a h) (fun a h => hju a h)

private theorem ext_of_mulVec_single {M M' : Matrix ι ι K}
    (h : ∀ j, M *ᵥ (Pi.single j (1 : K) : ι → K) =
      M' *ᵥ (Pi.single j (1 : K) : ι → K)) :
    M = M' := by
  ext i j
  have := congrFun (h j) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this

theorem conjMat_mul_swap [CharP K 2] {k : ℕ} {u w : Fin k → ι}
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    conjMat K u w * conjMat K w u = 1 := by
  apply ext_of_mulVec_single
  intro j
  by_cases hju : ∃ b, u b = j
  · obtain ⟨b, rfl⟩ := hju
    rw [← Matrix.mulVec_mulVec, conjMat_swap_mulVec_single_u hu hw huw,
      conjMat_mulVec_single_w hu hw huw, Matrix.one_mulVec]
  · by_cases hjw : ∃ b, w b = j
    · obtain ⟨b, rfl⟩ := hjw
      rw [← Matrix.mulVec_mulVec, conjMat_swap_mulVec_single_w hu hw huw, Matrix.mulVec_add,
        conjMat_mulVec_single_u hu hw huw, conjMat_mulVec_single_w hu hw huw,
        Matrix.one_mulVec, add_add_self_eq']
    · rw [← Matrix.mulVec_mulVec,
        conjMat_swap_mulVec_single_of_forall_ne j
          (fun a h => hju ⟨a, h⟩) (fun a h => hjw ⟨a, h⟩),
        conjMat_mulVec_single_of_forall_ne j
          (fun a h => hju ⟨a, h⟩) (fun a h => hjw ⟨a, h⟩),
        Matrix.one_mulVec]

noncomputable def swapFun {k : ℕ} (u w : Fin k → ι) : ι → ι :=
  fun i => if h : ∃ a, u a = i then w (Classical.choose h)
    else if h : ∃ a, w a = i then u (Classical.choose h) else i

omit [Fintype ι] in
theorem swapFun_apply_left {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (a : Fin k) :
    swapFun u w (u a) = w a := by
  rw [swapFun]
  have hex : ∃ b, u b = u a := ⟨a, rfl⟩
  rw [dif_pos hex]
  exact congrArg w (hu (Classical.choose_spec hex))

omit [Fintype ι] in
theorem swapFun_apply_right {k : ℕ} {u w : Fin k → ι}
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (a : Fin k) :
    swapFun u w (w a) = u a := by
  rw [swapFun]
  have h1 : ¬ ∃ b, u b = w a := fun ⟨b, hb⟩ => huw b a hb
  have h2 : ∃ b, w b = w a := ⟨a, rfl⟩
  rw [dif_neg h1, dif_pos h2]
  exact congrArg u (hw (Classical.choose_spec h2))

omit [Fintype ι] in
theorem swapFun_apply_of_forall_ne {k : ℕ} {u w : Fin k → ι}
    (i : ι) (hi : ∀ a, i ≠ u a ∧ i ≠ w a) :
    swapFun u w i = i := by
  rw [swapFun]
  have h1 : ¬ ∃ a, u a = i := fun ⟨a, ha⟩ => (hi a).1 ha.symm
  have h2 : ¬ ∃ a, w a = i := fun ⟨a, ha⟩ => (hi a).2 ha.symm
  rw [dif_neg h1, dif_neg h2]

omit [Fintype ι] in
theorem swapFun_involutive {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    Function.Involutive (swapFun u w) := by
  intro i
  rw [swapFun, swapFun]
  by_cases h1 : ∃ a, u a = i
  · rw [dif_pos h1]
    have h2 : ¬ ∃ b, u b = w (Classical.choose h1) :=
      fun ⟨b, hb⟩ => huw b (Classical.choose h1) hb
    rw [dif_neg h2]
    have h3 : ∃ b, w b = w (Classical.choose h1) := ⟨Classical.choose h1, rfl⟩
    rw [dif_pos h3]
    rw [show Classical.choose h3 = Classical.choose h1 from
      hw (Classical.choose_spec h3)]
    exact Classical.choose_spec h1
  · rw [dif_neg h1]
    by_cases h2 : ∃ a, w a = i
    · rw [dif_pos h2]
      have h3 : ∃ b, u b = u (Classical.choose h2) := ⟨Classical.choose h2, rfl⟩
      rw [dif_pos h3]
      rw [show Classical.choose h3 = Classical.choose h2 from
        hu (Classical.choose_spec h3)]
      exact Classical.choose_spec h2
    · rw [dif_neg h2, dif_neg h1, dif_neg h2]

noncomputable def swapPermOf {k : ℕ} (u w : Fin k → ι) (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) : Equiv.Perm ι :=
  Function.Involutive.toPerm (swapFun u w) (swapFun_involutive hu hw huw)

omit [Fintype ι] in
theorem swapPermOf_symm {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    (swapPermOf u w hu hw huw).symm = swapPermOf u w hu hw huw :=
  Function.Involutive.toPerm_symm _

omit [Fintype ι] in
theorem swapPermOf_apply_left {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (a : Fin k) :
    swapPermOf u w hu hw huw (u a) = w a := by
  change swapFun u w (u a) = w a
  exact swapFun_apply_left hu a

omit [Fintype ι] in
theorem swapPermOf_apply_right {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) (a : Fin k) :
    swapPermOf u w hu hw huw (w a) = u a := by
  change swapFun u w (w a) = u a
  exact swapFun_apply_right hw huw a

omit [Fintype ι] in
theorem swapPermOf_apply_of_forall_ne {k : ℕ} {u w : Fin k → ι}
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b)
    (i : ι) (hi : ∀ a, i ≠ u a ∧ i ≠ w a) :
    swapPermOf u w hu hw huw i = i := by
  change swapFun u w i = i
  exact swapFun_apply_of_forall_ne i hi

omit [Fintype ι] in
theorem swapPermOf_mul_self {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    swapPermOf u w hu hw huw * swapPermOf u w hu hw huw = 1 := by
  have hs : (swapPermOf u w hu hw huw).symm = swapPermOf u w hu hw huw := swapPermOf_symm hu hw huw
  simpa [Equiv.Perm.inv_def, hs] using _root_.mul_inv_cancel (swapPermOf u w hu hw huw)

theorem conjMat_eq_permMatrix_swap {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    conjMat K u w = (swapPermOf u w hu hw huw).permMatrix K * (1 + nilOf K w u) := by
  apply ext_of_mulVec_single
  intro j
  by_cases hju : ∃ b, u b = j
  · obtain ⟨b, rfl⟩ := hju
    have hP0 : (1 + nilOf K w u) *ᵥ (Pi.single (u b) (1 : K) : ι → K) =
        (Pi.single (u b) (1 : K) : ι → K) + Pi.single (w b) (1 : K) := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec,
        nilOf_mulVec_single_w (u := w) (w := u) hu b]
    rw [← Matrix.mulVec_mulVec, hP0, Matrix.mulVec_add, permMatrix_mulVec_single, swapPermOf_symm,
      swapPermOf_apply_left, permMatrix_mulVec_single, swapPermOf_symm,
      swapPermOf_apply_right, conjMat_mulVec_single_u hu hw huw]
    exact add_comm _ _
  · by_cases hjw : ∃ b, w b = j
    · obtain ⟨b, rfl⟩ := hjw
      have hP0 : (1 + nilOf K w u) *ᵥ (Pi.single (w b) (1 : K) : ι → K) =
          Pi.single (w b) (1 : K) := by
        rw [Matrix.add_mulVec, Matrix.one_mulVec,
          nilOf_mulVec_single_u (u := w) (w := u) (fun a c => (huw c a).symm) b, add_zero]
      rw [← Matrix.mulVec_mulVec, hP0, permMatrix_mulVec_single, swapPermOf_symm, swapPermOf_apply_right,
        conjMat_mulVec_single_w hu hw huw]
    · have hP0 : (1 + nilOf K w u) *ᵥ (Pi.single j (1 : K) : ι → K) =
          Pi.single j (1 : K) :=
        one_add_nilOf_mulVec_single_of_forall_ne (u := w) (w := u) j
          (fun a h => hju ⟨a, h⟩)
      rw [← Matrix.mulVec_mulVec, hP0, permMatrix_mulVec_single, swapPermOf_symm,
        swapPermOf_apply_of_forall_ne hu hw huw j
          (fun a => ⟨fun h => hju ⟨a, h.symm⟩, fun h => hjw ⟨a, h.symm⟩⟩),
        conjMat_mulVec_single_of_forall_ne j
          (fun a h => hju ⟨a, h⟩) (fun a h => hjw ⟨a, h⟩)]

theorem conjMat_det [CharP K 2] {k : ℕ} {u w : Fin k → ι} (hu : Function.Injective u)
    (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    (conjMat K u w).det = 1 := by
  rw [conjMat_eq_permMatrix_swap hu hw huw, Matrix.det_mul, det_permMatrix_of_charTwo,
    det_one_add_nilOf (u := w) (w := u) (fun a b => (huw b a).symm), one_mul]

theorem conjMat_conj_nilOf [CharP K 2] {k : ℕ} {u w : Fin k → ι}
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    conjMat K u w * (1 + nilOf K u w) * conjMat K w u =
      (swapPermOf u w hu hw huw).permMatrix K := by
  apply ext_of_mulVec_single
  intro j
  by_cases hju : ∃ b, u b = j
  · obtain ⟨b, rfl⟩ := hju
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      conjMat_swap_mulVec_single_u hu hw huw, one_add_nilOf_mulVec_single_w hw b,
      conjMat_mulVec_single_add_w_u hu hw huw, permMatrix_mulVec_single, swapPermOf_symm,
      swapPermOf_apply_left]
  · by_cases hjw : ∃ b, w b = j
    · obtain ⟨b, rfl⟩ := hjw
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        conjMat_swap_mulVec_single_w hu hw huw, one_add_nilOf_mulVec_single_add_u_w hw huw b,
        conjMat_mulVec_single_w hu hw huw, permMatrix_mulVec_single, swapPermOf_symm,
        swapPermOf_apply_right]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        conjMat_swap_mulVec_single_of_forall_ne j
          (fun a h => hju ⟨a, h⟩) (fun a h => hjw ⟨a, h⟩),
        one_add_nilOf_mulVec_single_of_forall_ne j (fun a h => hjw ⟨a, h⟩),
        conjMat_mulVec_single_of_forall_ne j
          (fun a h => hju ⟨a, h⟩) (fun a h => hjw ⟨a, h⟩),
        permMatrix_mulVec_single, swapPermOf_symm,
        swapPermOf_apply_of_forall_ne hu hw huw j
          (fun a => ⟨fun h => hju ⟨a, h.symm⟩, fun h => hjw ⟨a, h.symm⟩⟩)]

theorem exists_conj_one_add_nilOf_eq_permMatrix_sl [CharP K 2] {k : ℕ} (u w : Fin k → ι)
    (hu : Function.Injective u) (hw : Function.Injective w) (huw : ∀ a b, u a ≠ w b) :
    ∃ (σ : Equiv.Perm ι) (g : SpecialLinearGroup ι K), σ * σ = 1 ∧
      (∀ a, σ (u a) = w a) ∧ (∀ i, (∀ a, i ≠ u a ∧ i ≠ w a) → σ i = i) ∧
      (g : Matrix ι ι K) * (1 + nilOf K u w) *
          ((g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) = σ.permMatrix K := by
  classical
  let σ : Equiv.Perm ι := swapPermOf u w hu hw huw
  let h : Matrix ι ι K := conjMat K u w
  have hdet : h.det = 1 := conjMat_det hu hw huw
  let g : SpecialLinearGroup ι K := ⟨h, hdet⟩
  have hgval : (g : Matrix ι ι K) = h := rfl
  have hginv : ((g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) = conjMat K w u := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hgval, adjugate_eq_inv_of_det_eq_one hdet,
      Matrix.inv_eq_right_inv (conjMat_mul_swap hu hw huw)]
  refine ⟨σ, g, ?_, ?_, ?_, ?_⟩
  · simpa [σ] using swapPermOf_mul_self hu hw huw
  · simpa [σ] using swapPermOf_apply_left hu hw huw
  · simpa [σ] using swapPermOf_apply_of_forall_ne hu hw huw
  · rw [hgval, hginv]
    simpa [h, σ] using conjMat_conj_nilOf hu hw huw

theorem exists_conj_eq_permMatrix [Finite K] [CharP K 2] {x : SpecialLinearGroup ι K}
    (hx : x * x = 1) :
    ∃ (σ : Equiv.Perm ι) (g : SpecialLinearGroup ι K), σ * σ = 1 ∧
      ((g * x * g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) = σ.permMatrix K := by
  obtain ⟨k, u, w, hu, hw, huw, g₁, hg₁⟩ :=
    CFSG.SeitzReduction.LinearPilot.exists_conj_eq_one_add_nilOf (K := K) hx
  obtain ⟨σ, g₂, hσ2, hσu, hσfix, hconj⟩ :=
    exists_conj_one_add_nilOf_eq_permMatrix_sl (K := K) u w hu hw huw
  refine ⟨σ, g₂ * g₁, hσ2, ?_⟩
  have hgroup : (g₂ * g₁) * x * (g₂ * g₁)⁻¹ = g₂ * (g₁ * x * g₁⁻¹) * g₂⁻¹ := by
    rw [_root_.mul_inv_rev]
    simp only [mul_assoc]
  calc (((g₂ * g₁) * x * (g₂ * g₁)⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K)
      = ((g₂ * (g₁ * x * g₁⁻¹) * g₂⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) := by
          rw [hgroup]
    _ = (g₂ : Matrix ι ι K) * ((g₁ * x * g₁⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) *
          ((g₂⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) := by
          simp only [Matrix.SpecialLinearGroup.coe_mul]
    _ = (g₂ : Matrix ι ι K) * (1 + nilOf K u w) *
          ((g₂⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) := by rw [hg₁]
    _ = σ.permMatrix K := hconj

theorem exists_conj_eq_permMatrix_of_ne_one [Finite K] [CharP K 2] {n : ℕ}
    {x : SpecialLinearGroup (Fin (n + 2)) K} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ (σ : Equiv.Perm (Fin (n + 2))) (g : SpecialLinearGroup (Fin (n + 2)) K), σ * σ = 1 ∧
      σ 0 = 1 ∧
      ((g * x * g⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) K) = σ.permMatrix K := by
  obtain ⟨σ, g, hσ2, hconj⟩ := exists_conj_eq_permMatrix (K := K) (ι := Fin (n + 2)) hx
  have hσne : σ ≠ 1 := by
    intro hσ1
    apply hx1
    have hmat : ((g * x * g⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) K) = 1 := by
      rw [hconj, hσ1, Matrix.permMatrix_one]
    have hgxg : g * x * g⁻¹ = 1 := Subtype.ext hmat
    have hgx : g * x = g := by
      have := congrArg (fun y : SpecialLinearGroup (Fin (n + 2)) K => y * g) hgxg
      simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using this
    have h := congrArg (fun y : SpecialLinearGroup (Fin (n + 2)) K => g⁻¹ * y) hgx
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    apply hσne
    ext j
    by_contra hj
    exact h ⟨j, fun hjj => hj (by simp [hjj])⟩
  let f : Bool → Fin (n + 2) := fun t => if t then 1 else 0
  let v : Bool → Fin (n + 2) := fun t => if t then σ i else i
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b <;> simp_all [f, Fin.ext_iff]
  have hv : Function.Injective v := by
    intro a b hab
    cases a <;> cases b <;> simp_all [v, Fin.ext_iff]
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f v hf hv
  have hπ0 : π 0 = i := by simpa [f, v] using hπ false
  have hπ1 : π 1 = σ i := by simpa [f, v] using hπ true
  let Pπ : SpecialLinearGroup (Fin (n + 2)) K :=
    ⟨π.permMatrix K, det_permMatrix_of_charTwo π⟩
  have hPπinv : ((Pπ⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
      Matrix (Fin (n + 2)) (Fin (n + 2)) K) = (π⁻¹).permMatrix K := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    change (π.permMatrix K).adjugate = (π⁻¹).permMatrix K
    rw [adjugate_eq_inv_of_det_eq_one (det_permMatrix_of_charTwo (K := K) π)]
    refine Matrix.inv_eq_right_inv ?_
    rw [← Matrix.permMatrix_mul (σ := π⁻¹) (τ := π),
      show π⁻¹ * π = (1 : Equiv.Perm (Fin (n + 2))) from inv_mul_cancel π,
      Matrix.permMatrix_one]
  have hτ2 : (π⁻¹ * σ * π) * (π⁻¹ * σ * π) = 1 := by
    have h : (π⁻¹ * σ * π) * (π⁻¹ * σ * π) = π⁻¹ * (σ * σ) * π := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [h, hσ2]
    simp
  have hτ0 : (π⁻¹ * σ * π) 0 = 1 := by
    simp [Equiv.Perm.mul_def, hπ0, ← hπ1]
  have hτP : (Pπ : Matrix (Fin (n + 2)) (Fin (n + 2)) K) * (σ.permMatrix K) *
      ((Pπ⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) K) =
      (π⁻¹ * σ * π).permMatrix K := by
    rw [hPπinv]
    change π.permMatrix K * σ.permMatrix K * (π⁻¹).permMatrix K =
      (π⁻¹ * σ * π).permMatrix K
    rw [← Matrix.permMatrix_mul (σ := σ) (τ := π),
      ← Matrix.permMatrix_mul (σ := π⁻¹) (τ := σ * π)]
    congr 1
  have hgroup : (Pπ * g) * x * (Pπ * g)⁻¹ = Pπ * (g * x * g⁻¹) * Pπ⁻¹ := by
    rw [_root_.mul_inv_rev]
    simp only [mul_assoc]
  refine ⟨π⁻¹ * σ * π, Pπ * g, hτ2, hτ0, ?_⟩
  calc (((Pπ * g) * x * (Pπ * g)⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) K)
      = ((Pπ * (g * x * g⁻¹) * Pπ⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
          Matrix (Fin (n + 2)) (Fin (n + 2)) K) := by rw [hgroup]
    _ = (Pπ : Matrix (Fin (n + 2)) (Fin (n + 2)) K) *
          ((g * x * g⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) K) *
          ((Pπ⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) K) := by
          simp only [Matrix.SpecialLinearGroup.coe_mul]
    _ = (Pπ : Matrix (Fin (n + 2)) (Fin (n + 2)) K) * (σ.permMatrix K) *
          ((Pπ⁻¹ : SpecialLinearGroup (Fin (n + 2)) K) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) K) := by rw [hconj]
    _ = (π⁻¹ * σ * π).permMatrix K := hτP

end CFSG.LieType.SpecialLinear
