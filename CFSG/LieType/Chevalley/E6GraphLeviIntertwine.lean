module

public import CFSG.LieType.Chevalley.E6GraphLeviModel
public import CFSG.LieType.Chevalley.C2E6RootOperators

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphLevi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.ExteriorCube Matrix

variable {E : Type} [Field E]

theorem xOp_hVec' (i j : Fin TwistTag.E6.tag.rank) (c : E) :
    xOp TwistTag.E6.tag E i c (hVec TwistTag.E6.tag E j) = hVec TwistTag.E6.tag E j +
      (((TwistTag.E6.tag.cartan j i).natAbs : E) * c) •
        rootVec TwistTag.E6.tag E (Pi.single i 1) := by
  change xOp _ _ i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

theorem yOp_hVec' (i j : Fin TwistTag.E6.tag.rank) (c : E) :
    yOp TwistTag.E6.tag E i c (hVec TwistTag.E6.tag E j) = hVec TwistTag.E6.tag E j +
      (((TwistTag.E6.tag.cartan j i).natAbs : E) * c) •
        rootVec TwistTag.E6.tag E (-Pi.single i 1) := by
  change yOp _ _ i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

theorem xOp_rootVec_single' (i : Fin TwistTag.E6.tag.rank) (c : E) :
    xOp TwistTag.E6.tag E i c (rootVec TwistTag.E6.tag E (Pi.single i 1)) =
      rootVec TwistTag.E6.tag E (Pi.single i 1) := by
  rw [rootVec_eq_single' (isRoot_single _ i), xOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

theorem yOp_rootVec_neg_single' (i : Fin TwistTag.E6.tag.rank) (c : E) :
    yOp TwistTag.E6.tag E i c (rootVec TwistTag.E6.tag E (-Pi.single i 1)) =
      rootVec TwistTag.E6.tag E (-Pi.single i 1) := by
  rw [rootVec_eq_single' (isRoot_neg_single _ i), yOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

theorem xOp_rootVec_neg_single''
    (i : Fin TwistTag.E6.tag.rank) (c : E) :
    xOp TwistTag.E6.tag E i c (rootVec TwistTag.E6.tag E (-Pi.single i 1)) =
      rootVec TwistTag.E6.tag E (-Pi.single i 1) + c • hVec TwistTag.E6.tag E i +
        c ^ 2 • rootVec TwistTag.E6.tag E (Pi.single i 1) := by
  rw [rootVec_eq_single' (isRoot_neg_single _ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

theorem yOp_rootVec_single'' (i : Fin TwistTag.E6.tag.rank) (c : E) :
    yOp TwistTag.E6.tag E i c (rootVec TwistTag.E6.tag E (Pi.single i 1)) =
      rootVec TwistTag.E6.tag E (Pi.single i 1) + c • hVec TwistTag.E6.tag E i +
        c ^ 2 • rootVec TwistTag.E6.tag E (-Pi.single i 1) := by
  rw [rootVec_eq_single' (isRoot_single _ i), yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

theorem xOp_rootVec_of_ne
    (i : Fin TwistTag.E6.tag.rank) (c : E) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1) :
    xOp TwistTag.E6.tag E i c (rootVec TwistTag.E6.tag E β) =
      rootVec TwistTag.E6.tag E β + c • rootVec TwistTag.E6.tag E (β + Pi.single i 1) :=
  C2E6Std.xOp_rootVec_E6 i c hβ h₁ h₂

theorem yOp_rootVec_of_ne
    (i : Fin TwistTag.E6.tag.rank) (c : E) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1) :
    yOp TwistTag.E6.tag E i c (rootVec TwistTag.E6.tag E β) =
      rootVec TwistTag.E6.tag E β + c • rootVec TwistTag.E6.tag E (β - Pi.single i 1) :=
  C2E6Std.yOp_rootVec_E6 i c hβ h₁ h₂

theorem single_mul_diagonal' (i j : Fin 6) (c : E) (d : Fin 6 → E) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · rw [ite_eq_left h, ite_eq_left h, h.2]
  · rw [ite_eq_right h, ite_eq_right h, zero_mul]

theorem diagonal_mul_single' (i j : Fin 6) (c : E) (d : Fin 6 → E) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · rw [ite_eq_left h, ite_eq_left h, h.1]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]


theorem natCast_cartan_x (h2 : (2 : E) = 0) (j : Fin 6) (t : Fin 5) :
    (((TwistTag.E6.tag.cartan (e6Idx j) (pathIdx t)).natAbs : ℕ) : E) =
      (diagCoeff j t.castSucc : E) + (diagCoeff j t.succ : E) := by
  have h := cartan_diagCoeff j t
  have hc : (((TwistTag.E6.tag.cartan (e6Idx j) (pathIdx t)).natAbs +
      diagCoeff j t.castSucc + diagCoeff j t.succ : ℕ) : E) = 0 := by
    rw [natCast_eq_mod_two E h2, h, Nat.cast_zero]
  push_cast at hc
  linear_combination hc - (diagCoeff j t.castSucc + diagCoeff j t.succ : E) * h2

theorem conj_x_single (h2 : (2 : E) = 0) (t : Fin 5) (c : E) (a b : Fin 6) :
    xMat t c * Matrix.single a b 1 * xMat t (-c) = Matrix.single a b 1 +
      ((if t.succ = a then Matrix.single t.castSucc b c else 0) +
        ((if b = t.castSucc then Matrix.single a t.succ c else 0) +
          (if t.succ = a ∧ b = t.castSucc then Matrix.single t.castSucc t.succ (c * c)
            else 0))) := by
  rw [transvection_conj]
  have hneg : ∀ M : Matrix (Fin 6) (Fin 6) E, -M = M := fun M => by
    ext x y
    exact neg_eq_self_of_two h2 _
  have hts : t.succ ≠ t.castSucc := (castSucc_ne_succ t).symm
  by_cases ha : t.succ = a <;> by_cases hb : b = t.castSucc
  · subst ha hb
    simp only [single_mul_single', ite_true, and_self, mul_one, one_mul]
    rw [sub_eq_add_neg, sub_eq_add_neg, hneg, hneg]
    abel
  · simp [ha, hb]
  · simp only [single_mul_single', ha, hb, ite_true, ite_false, false_and, one_mul, zero_mul,
      sub_zero, add_zero, zero_add]
    rw [sub_eq_add_neg, hneg]
  · simp [ha, hb]


theorem diagonal_coeff_path (t : Fin 5) :
    (Matrix.diagonal fun i => (diagCoeff (pathIdx t) i : E)) =
      Matrix.single t.castSucc t.castSucc 1 + Matrix.single t.succ t.succ 1 := by
  have h : (fun i => (diagCoeff (pathIdx t) i : E)) =
      Pi.single t.castSucc 1 + Pi.single t.succ 1 := by
    funext i
    rw [diagCoeff_path, Pi.add_apply]
    by_cases h1 : i = t.castSucc
    · subst h1
      simp [castSucc_ne_succ t]
    · by_cases h2 : i = t.succ
      · subst h2
        simp [(castSucc_ne_succ t).symm]
      · simp [h1, h2]
  rw [h, show (Pi.single t.castSucc 1 + Pi.single t.succ 1 : Fin 6 → E) =
    fun i => Pi.single t.castSucc (1 : E) i + Pi.single t.succ (1 : E) i from rfl,
    ← Matrix.diagonal_add, Matrix.diagonal_single, Matrix.diagonal_single]

theorem modelLin_xMat_mat (B B' : Matrix (Fin 6) (Fin 6) E) (A : Matrix (Fin 6) (Fin 6) E) :
    modelLin B B' ((A, 0, 0, 0, 0) : Model E) = (B * A * B', 0, 0, 0, 0) := by
  rw [modelLin_apply]
  simp

theorem modelLin_x_hImage (h2 : (2 : E) = 0) (t : Fin 5) (c : E) (j : Fin 6) :
    modelLin (xMat t c) (xMat t (-c)) (hImage (e6Idx j)) =
      hImage (e6Idx j) + (((TwistTag.E6.tag.cartan (e6Idx j) (pathIdx t)).natAbs : E) * c) •
        rootImage (Pi.single (pathIdx t) 1) := by
  rw [← matRoot_adjacent, rootImage_matRoot (castSucc_ne_succ t), hImage, modelLin_xMat_mat,
    transvection_conj, single_mul_diagonal', diagonal_mul_single', single_mul_single',
    ite_eq_right (castSucc_ne_succ t).symm, natCast_cartan_x h2]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · simp only [Prod.fst_add, Prod.smul_fst, sub_zero, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [sub_eq_add_neg, Matrix.single_neg, add_assoc, ← Matrix.single_add]
    congr 2
    linear_combination (-(diagCoeff j t.castSucc : E) * c) * h2
  · simp
  · simp
  · simp
  · simp


theorem modelLin_xMat_line (B B' : Matrix (Fin 6) (Fin 6) E) (a b : E) :
    modelLin B B' ((0, a, b, 0, 0) : Model E) = (0, a, b, 0, 0) := by
  rw [modelLin_apply]
  simp

theorem modelLin_xMat_cubeP (B B' : Matrix (Fin 6) (Fin 6) E) (u : ⋀[E]^3 (Fin 6 → E)) :
    modelLin B B' ((0, 0, 0, u, 0) : Model E) =
      (0, 0, 0, exteriorPower.map 3 (Matrix.toLin' B) u, 0) := by
  rw [modelLin_apply]
  simp

theorem modelLin_xMat_cubeN (B B' : Matrix (Fin 6) (Fin 6) E) (u : ⋀[E]^3 (Fin 6 → E)) :
    modelLin B B' ((0, 0, 0, 0, u) : Model E) =
      (0, 0, 0, 0, exteriorPower.map 3 (Matrix.toLin' B) u) := by
  rw [modelLin_apply]
  simp

theorem modelLin_x_pos (h2 : (2 : E) = 0) (t : Fin 5) (c : E) :
    modelLin (xMat t c) (xMat t (-c)) (rootImage (Pi.single (pathIdx t) 1)) =
      rootImage (Pi.single (pathIdx t) 1) := by
  rw [← matRoot_adjacent, rootImage_matRoot (castSucc_ne_succ t), modelLin_xMat_mat,
    conj_x_single h2]
  have hts : t.succ ≠ t.castSucc := (castSucc_ne_succ t).symm
  simp [hts]

theorem modelLin_x_neg (h2 : (2 : E) = 0) (t : Fin 5) (c : E) :
    modelLin (xMat t c) (xMat t (-c)) (rootImage (-Pi.single (pathIdx t) 1)) =
      rootImage (-Pi.single (pathIdx t) 1) + c • hImage (pathIdx t) +
        c ^ 2 • rootImage (Pi.single (pathIdx t) 1) := by
  rw [← matRoot_adjacent_neg, ← matRoot_adjacent, rootImage_matRoot (castSucc_ne_succ t),
    rootImage_matRoot (castSucc_ne_succ t).symm, modelLin_xMat_mat, conj_x_single h2, hImage,
    diagonal_coeff_path]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · simp only [ite_true, and_self, Prod.fst_add, Prod.smul_fst, Matrix.smul_single, smul_eq_mul,
      mul_one, smul_add]
    rw [pow_two]
    abel
  · simp
  · simp
  · simp
  · simp


theorem adjacent_x (t : Fin 5) :
    t.castSucc.val + 1 = t.succ.val ∨ t.succ.val + 1 = t.castSucc.val :=
  Or.inl (by simp)

theorem modelLin_x_rootImage
    (h2 : (2 : E) = 0) (t : Fin 5) (c : E)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (h₁ : β ≠ Pi.single (pathIdx t) 1) (h₂ : β ≠ -Pi.single (pathIdx t) 1) :
    modelLin (xMat t c) (xMat t (-c)) (rootImage β) =
      rootImage β + c • rootImage (β + Pi.single (pathIdx t) 1) := by
  rcases root_cases β (mem_rootFinset.2 hβ) with ⟨a, b, hab, rfl⟩ | rfl | rfl |
    ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · have hne1 : ¬(a = t.castSucc ∧ b = t.succ) := fun ⟨ha, hb⟩ =>
      h₁ (by rw [ha, hb, matRoot_adjacent])
    have hne2 : ¬(a = t.succ ∧ b = t.castSucc) := fun ⟨ha, hb⟩ =>
      h₂ (by rw [ha, hb, matRoot_adjacent_neg])
    rw [rootImage_matRoot hab, modelLin_xMat_mat, conj_x_single h2]
    by_cases ha : a = t.succ
    · subst ha
      have hb : b ≠ t.castSucc := fun hb => hne2 ⟨rfl, hb⟩
      rw [matRoot_add_left t b hb (Ne.symm hab), rootImage_matRoot (Ne.symm hb)]
      simp [hb]
    · by_cases hb : b = t.castSucc
      · subst hb
        rw [matRoot_add_right t a hab ha, rootImage_matRoot ha]
        simp [Ne.symm ha]
      · rw [rootImage_of_not_isRoot fun h =>
          matRoot_add_not t a b hab ha hb hne1 (mem_rootFinset.2 h)]
        simp [Ne.symm ha, hb]
  · have hn : ¬IsRoot TwistTag.E6.tag (e6HighestRoot + Pi.single (pathIdx t) 1) := fun h =>
      (not_isRoot_e6HighestRoot_add t).1 (mem_rootFinset.2 h)
    rw [rootImage_e6HighestRoot, modelLin_xMat_line, rootImage_of_not_isRoot hn, smul_zero,
      add_zero]
  · have hn : ¬IsRoot TwistTag.E6.tag (-e6HighestRoot + Pi.single (pathIdx t) 1) := fun h =>
      (not_isRoot_e6HighestRoot_add t).2.2.1 (mem_rootFinset.2 h)
    rw [rootImage_neg_e6HighestRoot, modelLin_xMat_line, rootImage_of_not_isRoot hn, smul_zero,
      add_zero]
  · set S' : Set.powersetCard (Fin 6) 3 := ⟨S, Set.powersetCard.mem_iff.2 hS⟩
    have hS' : cubeRoot S = cubeRoot S'.1 := rfl
    rw [hS', rootImage_cubeRoot, modelLin_xMat_cubeP, ← wedgeBasis_eq_basis,
      map_transvection_wedgeBasis (adjacent_x t)]
    by_cases h : t.succ ∈ S'.1 ∧ t.castSucc ∉ S'.1
    · rw [dite_eq_left h, cubeRoot_add_eq S t hS h.1 h.2]
      have := rootImage_cubeRoot (E := E) (replace S' h.1 h.2)
      rw [show (replace S' h.1 h.2).1 = insert t.castSucc (S.erase t.succ) from rfl] at this
      rw [this, wedgeBasis_eq_basis, wedgeBasis_eq_basis]
      simp
    · rw [dite_eq_right h, rootImage_of_not_isRoot fun h' =>
        cubeRoot_add_not S t hS h (mem_rootFinset.2 h'), wedgeBasis_eq_basis]
      simp
  · set S' : Set.powersetCard (Fin 6) 3 := ⟨S, Set.powersetCard.mem_iff.2 hS⟩
    have hS' : -cubeRoot Sᶜ = -cubeRoot S'.1ᶜ := rfl
    rw [hS', rootImage_neg_cubeRoot, modelLin_xMat_cubeN, ← wedgeBasis_eq_basis,
      map_transvection_wedgeBasis (adjacent_x t)]
    by_cases h : t.succ ∈ S'.1 ∧ t.castSucc ∉ S'.1
    · rw [dite_eq_left h, negCube_add_eq S t hS h.1 h.2]
      have := rootImage_neg_cubeRoot (E := E) (replace S' h.1 h.2)
      rw [show (replace S' h.1 h.2).1 = insert t.castSucc (S.erase t.succ) from rfl] at this
      rw [this, wedgeBasis_eq_basis, wedgeBasis_eq_basis]
      simp
    · rw [dite_eq_right h, rootImage_of_not_isRoot fun h' =>
        negCube_add_not S t hS h (mem_rootFinset.2 h'), wedgeBasis_eq_basis]
      simp


theorem toModel_comp_xOp
    (h2 : (2 : E) = 0) (t : Fin 5) (c : E) :
    toModel ∘ₗ xOp TwistTag.E6.tag E (pathIdx t) c =
      modelLin (xMat t c) (xMat t (-c)) ∘ₗ toModel := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨β, hβ⟩
  · rw [show (Finsupp.single (Sum.inl j) 1 : RootModule TwistTag.E6.tag E) =
      hVec TwistTag.E6.tag E (e6Idx j) from rfl, xOp_hVec', map_add, map_smul, toModel_hVec,
      toModel_rootVec]
    exact (modelLin_x_hImage h2 t c j).symm
  · rw [← rootVec_eq_single' hβ, toModel_rootVec]
    by_cases h₁ : β = Pi.single (pathIdx t) 1
    · subst h₁
      rw [xOp_rootVec_single', toModel_rootVec, modelLin_x_pos h2]
    · by_cases h₂ : β = -Pi.single (pathIdx t) 1
      · subst h₂
        rw [xOp_rootVec_neg_single'', map_add, map_add, map_smul, map_smul, toModel_rootVec,
          toModel_rootVec, toModel_hVec, modelLin_x_neg h2]
      · rw [xOp_rootVec_of_ne _ c hβ h₁ h₂, map_add, map_smul, toModel_rootVec, toModel_rootVec,
          modelLin_x_rootImage h2 t c hβ h₁ h₂]


theorem conj_y_single (h2 : (2 : E) = 0) (t : Fin 5) (c : E) (a b : Fin 6) :
    yMat t c * Matrix.single a b 1 * yMat t (-c) = Matrix.single a b 1 +
      ((if t.castSucc = a then Matrix.single t.succ b c else 0) +
        ((if b = t.succ then Matrix.single a t.castSucc c else 0) +
          (if t.castSucc = a ∧ b = t.succ then Matrix.single t.succ t.castSucc (c * c)
            else 0))) := by
  rw [transvection_conj]
  have hneg : ∀ M : Matrix (Fin 6) (Fin 6) E, -M = M := fun M => by
    ext x y
    exact neg_eq_self_of_two h2 _
  by_cases ha : t.castSucc = a <;> by_cases hb : b = t.succ
  · subst ha hb
    simp only [single_mul_single', ite_true, and_self, mul_one, one_mul]
    rw [sub_eq_add_neg, sub_eq_add_neg, hneg, hneg]
    abel
  · simp [ha, hb]
  · simp only [single_mul_single', ha, hb, ite_true, ite_false, false_and, one_mul, zero_mul,
      sub_zero, add_zero, zero_add]
    rw [sub_eq_add_neg, hneg]
  · simp [ha, hb]

theorem modelLin_y_hImage (h2 : (2 : E) = 0) (t : Fin 5) (c : E) (j : Fin 6) :
    modelLin (yMat t c) (yMat t (-c)) (hImage (e6Idx j)) =
      hImage (e6Idx j) + (((TwistTag.E6.tag.cartan (e6Idx j) (pathIdx t)).natAbs : E) * c) •
        rootImage (-Pi.single (pathIdx t) 1) := by
  rw [← matRoot_adjacent_neg, rootImage_matRoot (castSucc_ne_succ t).symm, hImage,
    modelLin_xMat_mat, transvection_conj, single_mul_diagonal', diagonal_mul_single',
    single_mul_single', ite_eq_right (castSucc_ne_succ t), natCast_cartan_x h2]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · simp only [Prod.fst_add, Prod.smul_fst, sub_zero, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [sub_eq_add_neg, Matrix.single_neg, add_assoc, ← Matrix.single_add]
    congr 2
    linear_combination (-(diagCoeff j t.succ : E) * c) * h2
  · simp
  · simp
  · simp
  · simp

theorem modelLin_y_neg (h2 : (2 : E) = 0) (t : Fin 5) (c : E) :
    modelLin (yMat t c) (yMat t (-c)) (rootImage (-Pi.single (pathIdx t) 1)) =
      rootImage (-Pi.single (pathIdx t) 1) := by
  rw [← matRoot_adjacent_neg, rootImage_matRoot (castSucc_ne_succ t).symm, modelLin_xMat_mat,
    conj_y_single h2]
  simp [castSucc_ne_succ t]

theorem modelLin_y_pos (h2 : (2 : E) = 0) (t : Fin 5) (c : E) :
    modelLin (yMat t c) (yMat t (-c)) (rootImage (Pi.single (pathIdx t) 1)) =
      rootImage (Pi.single (pathIdx t) 1) + c • hImage (pathIdx t) +
        c ^ 2 • rootImage (-Pi.single (pathIdx t) 1) := by
  rw [← matRoot_adjacent_neg, ← matRoot_adjacent, rootImage_matRoot (castSucc_ne_succ t),
    rootImage_matRoot (castSucc_ne_succ t).symm, modelLin_xMat_mat, conj_y_single h2, hImage,
    diagonal_coeff_path]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · simp only [ite_true, and_self, Prod.fst_add, Prod.smul_fst, Matrix.smul_single, smul_eq_mul,
      mul_one, smul_add]
    rw [pow_two]
    abel
  · simp
  · simp
  · simp
  · simp

theorem adjacent_y (t : Fin 5) :
    t.succ.val + 1 = t.castSucc.val ∨ t.castSucc.val + 1 = t.succ.val :=
  Or.inr (by simp)

theorem modelLin_y_rootImage
    (h2 : (2 : E) = 0) (t : Fin 5) (c : E)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (h₁ : β ≠ Pi.single (pathIdx t) 1) (h₂ : β ≠ -Pi.single (pathIdx t) 1) :
    modelLin (yMat t c) (yMat t (-c)) (rootImage β) =
      rootImage β + c • rootImage (β - Pi.single (pathIdx t) 1) := by
  rcases root_cases β (mem_rootFinset.2 hβ) with ⟨a, b, hab, rfl⟩ | rfl | rfl |
    ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · have hne1 : ¬(a = t.castSucc ∧ b = t.succ) := fun ⟨ha, hb⟩ =>
      h₁ (by rw [ha, hb, matRoot_adjacent])
    have hne2 : ¬(a = t.succ ∧ b = t.castSucc) := fun ⟨ha, hb⟩ =>
      h₂ (by rw [ha, hb, matRoot_adjacent_neg])
    rw [rootImage_matRoot hab, modelLin_xMat_mat, conj_y_single h2]
    by_cases ha : a = t.castSucc
    · subst ha
      have hb : b ≠ t.succ := fun hb => hne1 ⟨rfl, hb⟩
      rw [matRoot_sub_left t b (Ne.symm hab) hb, rootImage_matRoot (Ne.symm hb)]
      simp [hb]
    · by_cases hb : b = t.succ
      · subst hb
        rw [matRoot_sub_right t a ha hab, rootImage_matRoot ha]
        simp [Ne.symm ha]
      · rw [rootImage_of_not_isRoot fun h =>
          matRoot_sub_not t a b hab ha hb hne2 (mem_rootFinset.2 h)]
        simp [Ne.symm ha, hb]
  · have hn : ¬IsRoot TwistTag.E6.tag (e6HighestRoot - Pi.single (pathIdx t) 1) := fun h =>
      (not_isRoot_e6HighestRoot_add t).2.1 (mem_rootFinset.2 h)
    rw [rootImage_e6HighestRoot, modelLin_xMat_line, rootImage_of_not_isRoot hn, smul_zero,
      add_zero]
  · have hn : ¬IsRoot TwistTag.E6.tag (-e6HighestRoot - Pi.single (pathIdx t) 1) := fun h =>
      (not_isRoot_e6HighestRoot_add t).2.2.2 (mem_rootFinset.2 h)
    rw [rootImage_neg_e6HighestRoot, modelLin_xMat_line, rootImage_of_not_isRoot hn, smul_zero,
      add_zero]
  · set S' : Set.powersetCard (Fin 6) 3 := ⟨S, Set.powersetCard.mem_iff.2 hS⟩
    have hS' : cubeRoot S = cubeRoot S'.1 := rfl
    rw [hS', rootImage_cubeRoot, modelLin_xMat_cubeP, ← wedgeBasis_eq_basis,
      map_transvection_wedgeBasis (adjacent_y t)]
    by_cases h : t.castSucc ∈ S'.1 ∧ t.succ ∉ S'.1
    · rw [dite_eq_left h, cubeRoot_sub_eq S t hS h.1 h.2]
      have := rootImage_cubeRoot (E := E) (replace S' h.1 h.2)
      rw [show (replace S' h.1 h.2).1 = insert t.succ (S.erase t.castSucc) from rfl] at this
      rw [this, wedgeBasis_eq_basis, wedgeBasis_eq_basis]
      simp
    · rw [dite_eq_right h, rootImage_of_not_isRoot fun h' =>
        cubeRoot_sub_not S t hS h (mem_rootFinset.2 h'), wedgeBasis_eq_basis]
      simp
  · set S' : Set.powersetCard (Fin 6) 3 := ⟨S, Set.powersetCard.mem_iff.2 hS⟩
    have hS' : -cubeRoot Sᶜ = -cubeRoot S'.1ᶜ := rfl
    rw [hS', rootImage_neg_cubeRoot, modelLin_xMat_cubeN, ← wedgeBasis_eq_basis,
      map_transvection_wedgeBasis (adjacent_y t)]
    by_cases h : t.castSucc ∈ S'.1 ∧ t.succ ∉ S'.1
    · rw [dite_eq_left h, negCube_sub_eq S t hS h.1 h.2]
      have := rootImage_neg_cubeRoot (E := E) (replace S' h.1 h.2)
      rw [show (replace S' h.1 h.2).1 = insert t.succ (S.erase t.castSucc) from rfl] at this
      rw [this, wedgeBasis_eq_basis, wedgeBasis_eq_basis]
      simp
    · rw [dite_eq_right h, rootImage_of_not_isRoot fun h' =>
        negCube_sub_not S t hS h (mem_rootFinset.2 h'), wedgeBasis_eq_basis]
      simp

theorem toModel_comp_yOp
    (h2 : (2 : E) = 0) (t : Fin 5) (c : E) :
    toModel ∘ₗ yOp TwistTag.E6.tag E (pathIdx t) c =
      modelLin (yMat t c) (yMat t (-c)) ∘ₗ toModel := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨β, hβ⟩
  · rw [show (Finsupp.single (Sum.inl j) 1 : RootModule TwistTag.E6.tag E) =
      hVec TwistTag.E6.tag E (e6Idx j) from rfl, yOp_hVec', map_add, map_smul, toModel_hVec,
      toModel_rootVec]
    exact (modelLin_y_hImage h2 t c j).symm
  · rw [← rootVec_eq_single' hβ, toModel_rootVec]
    by_cases h₂ : β = -Pi.single (pathIdx t) 1
    · subst h₂
      rw [yOp_rootVec_neg_single', toModel_rootVec, modelLin_y_neg h2]
    · by_cases h₁ : β = Pi.single (pathIdx t) 1
      · subst h₁
        rw [yOp_rootVec_single'', map_add, map_add, map_smul, map_smul, toModel_rootVec,
          toModel_rootVec, toModel_hVec, modelLin_y_pos h2]
      · rw [yOp_rootVec_of_ne _ c hβ h₁ h₂, map_add, map_smul, toModel_rootVec, toModel_rootVec,
          modelLin_y_rootImage h2 t c hβ h₁ h₂]


end CFSG.LieType.Chevalley.E6GraphLevi
