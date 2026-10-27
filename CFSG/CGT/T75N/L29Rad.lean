module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups

variable {F : Type} [Field F] {n : ℕ}

@[expose] def rowMat (j : Fin n) (a : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  1 + vecMulVec (Pi.single j 1) a

theorem rowMat_zero (j : Fin n) : rowMat j (0 : Fin n → F) = 1 := by
  simp [rowMat]

theorem rowMat_mul (j : Fin n) {a : Fin n → F} (ha : a j = 0) (b : Fin n → F) :
    rowMat j a * rowMat j b = rowMat j (a + b) := by
  unfold rowMat
  have h := vecMulVec_mul_vecMulVec (Pi.single j (1 : F)) a (Pi.single j 1) b
  rw [dotProduct_single_one, ha, zero_smul] at h
  have h2 : (1 + vecMulVec (Pi.single j (1 : F)) a) * (1 + vecMulVec (Pi.single j 1) b) =
      1 + vecMulVec (Pi.single j 1) a + vecMulVec (Pi.single j 1) b +
        vecMulVec (Pi.single j 1) a * vecMulVec (Pi.single j 1) b := by noncomm_ring
  rw [h2, h, vecMulVec_add, vecMulVec_zero]
  abel

theorem det_rowMat (j : Fin n) {a : Fin n → F} (ha : a j = 0) : (rowMat j a).det = 1 := by
  unfold rowMat
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_single, ha]
  simp

theorem sl_coe_inv_mul (g : SpecialLinearGroup (Fin n) F) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (g : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]

theorem sl_coe_mul_inv (g : SpecialLinearGroup (Fin n) F) :
    (g : Matrix (Fin n) (Fin n) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]

@[expose] def rowSL (j : Fin n) (a : Fin n → F) (ha : a j = 0) : SpecialLinearGroup (Fin n) F :=
  ⟨rowMat j a, det_rowMat j ha⟩

@[simp] theorem coe_rowSL (j : Fin n) (a : Fin n → F) (ha : a j = 0) :
    ((rowSL j a ha : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = rowMat j a := rfl

@[expose] def radRow (n : ℕ) (F : Type) [Field F] (j : Fin n) :
    Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | ∃ a : Fin n → F, (∀ i, i ≤ j → a i = 0) ∧
    (g : Matrix (Fin n) (Fin n) F) = rowMat j a}
  one_mem' := ⟨0, fun _ _ => rfl, by simp [rowMat_zero]⟩
  mul_mem' := by
    rintro g h ⟨a, ha, hg⟩ ⟨b, hb, hh⟩
    refine ⟨a + b, fun i hi => by simp [ha i hi, hb i hi], ?_⟩
    rw [SpecialLinearGroup.coe_mul, hg, hh, rowMat_mul j (ha j le_rfl)]
  inv_mem' := by
    rintro g ⟨a, ha, hg⟩
    refine ⟨-a, fun i hi => by simp [ha i hi], ?_⟩
    have hinv : (g⁻¹ : SpecialLinearGroup (Fin n) F) = rowSL j (-a) (by simp [ha j le_rfl]) := by
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      rw [SpecialLinearGroup.coe_mul, hg, coe_rowSL, rowMat_mul j (ha j le_rfl), add_neg_cancel,
        rowMat_zero, SpecialLinearGroup.coe_one]
    rw [hinv]
    rfl

@[expose] def fixPt (n : ℕ) (F : Type) [Field F] (k : ℕ) :
    Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | ∀ i : Fin n, i.val < k →
    (g : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single i 1 : Fin n → F) = Pi.single i 1}
  one_mem' := by
    intro i _
    rw [SpecialLinearGroup.coe_one, one_mulVec]
  mul_mem' := by
    intro a b ha hb i hi
    rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hb i hi, ha i hi]
  inv_mem' := by
    intro a ha i hi
    conv_lhs => rw [← ha i hi]
    rw [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one,
      one_mulVec]

theorem fixPt_anti {j k : ℕ} (h : j ≤ k) : fixPt n F k ≤ fixPt n F j :=
  fun _ hg i hi => hg i (lt_of_lt_of_le hi h)

@[expose] def lowRows (n : ℕ) (F : Type) [Field F] (k : ℕ) :
    Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | ∀ i : Fin n, i.val < k → ∀ l,
    (g : Matrix (Fin n) (Fin n) F) i l = (1 : Matrix (Fin n) (Fin n) F) i l}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := by
    intro a b ha hb i hi l
    rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    simp_rw [ha i hi]
    rw [← Matrix.mul_apply, Matrix.one_mul]
    exact hb i hi l
  inv_mem' := by
    intro a ha i hi l
    have h1 := congrFun (congrFun (show ((a : Matrix (Fin n) (Fin n) F) *
      ((a⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)) = 1 by
        rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]) i) l
    rw [Matrix.mul_apply] at h1
    simp_rw [ha i hi] at h1
    rw [← Matrix.mul_apply, Matrix.one_mul] at h1
    exact h1

theorem lowRows_anti {j k : ℕ} (h : j ≤ k) : lowRows n F k ≤ lowRows n F j :=
  fun _ hg i hi => hg i (lt_of_lt_of_le hi h)

theorem radRow_le_fixPt (k : Fin n) : radRow n F k ≤ fixPt n F (k.val + 1) := by
  rintro g ⟨a, ha, hg⟩ i hi
  rw [hg]
  unfold rowMat
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, dotProduct_single_one,
    ha i (Fin.le_def.2 (Nat.lt_succ_iff.1 hi))]
  simp

theorem radRow_le_lowRows (j : Fin n) : radRow n F j ≤ lowRows n F j.val := by
  rintro g ⟨a, ha, hg⟩ i hi l
  rw [hg]
  have hij : i ≠ j := fun h => absurd hi (by rw [h]; exact lt_irrefl _)
  simp [rowMat, vecMulVec_apply, hij]

theorem radRow_inf_lowRows (k : Fin n) : radRow n F k ⊓ lowRows n F (k.val + 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨a, ha, hg⟩, hl⟩
  rw [Subgroup.mem_bot]
  have ha0 : a = 0 := by
    funext l
    have := hl k (Nat.lt_succ_self _) l
    rw [hg] at this
    simpa [rowMat, vecMulVec_apply] using this
  apply Subtype.ext
  rw [hg, ha0, rowMat_zero, SpecialLinearGroup.coe_one]

theorem conj_one_add_vecMulVec (g h : Matrix (Fin n) (Fin n) F) (hgh : g * h = 1)
    (u a : Fin n → F) :
    g * (1 + vecMulVec u a) * h = 1 + vecMulVec (g *ᵥ u) (a ᵥ* h) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgh, mul_vecMulVec, vecMulVec_mul]

theorem vecMul_apply_eq (a : Fin n → F) (M : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    (a ᵥ* M) i = a ⬝ᵥ (M *ᵥ (Pi.single i 1 : Fin n → F)) := by
  rw [mulVec_single_one]
  rfl

theorem conj_radRow_mem {j : Fin n} {k : ℕ} (hjk : j.val < k) {g : SpecialLinearGroup (Fin n) F}
    (hg : g ∈ fixPt n F k) {h : SpecialLinearGroup (Fin n) F} (hh : h ∈ radRow n F j) :
    g * h * g⁻¹ ∈ radRow n F j := by
  obtain ⟨a, ha, hh⟩ := hh
  have hgj : (g : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single j 1 : Fin n → F) = Pi.single j 1 :=
    hg j hjk
  have hginv : g⁻¹ ∈ fixPt n F k := (fixPt n F k).inv_mem hg
  refine ⟨a ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F), ?_, ?_⟩
  · intro i hi
    rw [vecMul_apply_eq, hginv i (lt_of_le_of_lt (Fin.le_def.1 hi) hjk), dotProduct_single_one,
      ha i hi]
  · rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hh]
    unfold rowMat
    rw [conj_one_add_vecMulVec _ _ (by rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one]), hgj]

section Card

variable [Finite F]

noncomputable def radRowEquiv (k : Fin n) :
    {a : Fin n → F // ∀ i, i ≤ k → a i = 0} ≃ radRow n F k :=
  Equiv.ofBijective
    (fun a => ⟨rowSL k a.1 (a.2 k le_rfl), ⟨a.1, a.2, rfl⟩⟩)
    ⟨fun a b hab => by
      have h := congrArg (fun g : radRow n F k =>
        ((g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)) hab
      simp only [coe_rowSL] at h
      apply Subtype.ext
      funext l
      have := congrFun (congrFun h k) l
      simpa [rowMat, vecMulVec_apply] using this,
     fun g => by
      obtain ⟨g, a, ha, hg⟩ := g
      refine ⟨⟨a, ha⟩, Subtype.ext (Subtype.ext ?_)⟩
      simp [hg]⟩

theorem card_radRow (k : Fin n) : Nat.card (radRow n F k) = Nat.card F ^ (n - 1 - k.val) := by
  classical
  have := Fintype.ofFinite F
  rw [← Nat.card_congr (radRowEquiv k),
    Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i b => i ≤ k → b = 0)), Nat.card_pi]
  have h1 : ∀ i : Fin n, Nat.card {b : F // i ≤ k → b = 0} = if i ≤ k then 1 else Nat.card F := by
    intro i
    by_cases hi : i ≤ k
    · simp only [hi, forall_true_left, ite_true]
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩, ⟨⟨0, rfl⟩⟩⟩
    · simp only [hi, false_imp_iff, ite_false]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have : (Finset.univ.filter fun i : Fin n => ¬ i ≤ k) = Finset.Ioi k := by
    ext i
    simp
  rw [this, Fin.card_Ioi]

end Card

section Swap

variable [NeZero n] [CharP F 2]

@[expose] def swapVec (j : Fin n) : Fin n → F := Pi.single 0 1 + Pi.single j 1

theorem swapVec_dot (j : Fin n) : swapVec j ⬝ᵥ swapVec j = (0 : F) := by
  unfold swapVec
  rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one]
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases hj : j = 0
  · subst hj
    simp [CharTwo.add_self_eq_zero]
  · simp [hj, Ne.symm hj, CharTwo.add_self_eq_zero]

@[expose] def swapMat (j : Fin n) : Matrix (Fin n) (Fin n) F :=
  1 + vecMulVec (swapVec j) (swapVec j)

theorem det_swapMat (j : Fin n) : (swapMat j : Matrix (Fin n) (Fin n) F).det = 1 := by
  unfold swapMat
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, swapVec_dot, add_zero]

theorem swapMat_mul_self (j : Fin n) : (swapMat j : Matrix (Fin n) (Fin n) F) * swapMat j = 1 := by
  unfold swapMat
  have h := vecMulVec_mul_vecMulVec (swapVec j : Fin n → F) (swapVec j) (swapVec j) (swapVec j)
  rw [swapVec_dot, zero_smul, vecMulVec_zero] at h
  have h2 : (1 + vecMulVec (swapVec j : Fin n → F) (swapVec j)) *
      (1 + vecMulVec (swapVec j) (swapVec j)) =
      1 + (vecMulVec (swapVec j) (swapVec j) + vecMulVec (swapVec j) (swapVec j)) +
        vecMulVec (swapVec j) (swapVec j) * vecMulVec (swapVec j) (swapVec j) := by noncomm_ring
  have h3 : vecMulVec (swapVec j : Fin n → F) (swapVec j) + vecMulVec (swapVec j) (swapVec j) =
      0 := by
    rw [← vecMulVec_add]
    have : (swapVec j : Fin n → F) + swapVec j = 0 := by
      funext i
      simp [CharTwo.add_self_eq_zero]
    rw [this, vecMulVec_zero]
  rw [h2, h, h3]
  simp

@[expose] def swapSL (j : Fin n) : SpecialLinearGroup (Fin n) F := ⟨swapMat j, det_swapMat j⟩

theorem swapSL_mul_self (j : Fin n) : (swapSL j : SpecialLinearGroup (Fin n) F) * swapSL j = 1 :=
  Subtype.ext (by
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one]
    exact swapMat_mul_self j)

theorem swapSL_inv (j : Fin n) : (swapSL j : SpecialLinearGroup (Fin n) F)⁻¹ = swapSL j :=
  inv_eq_of_mul_eq_one_right (swapSL_mul_self j)

theorem swapMat_mulVec (j : Fin n) :
    (swapMat j : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single j 1 : Fin n → F) = Pi.single 0 1 := by
  unfold swapMat
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec]
  by_cases hj : j = 0
  · subst hj
    simp [swapVec, CharTwo.add_self_eq_zero]
  · have h2 : (Pi.single j 1 : Fin n → F) + Pi.single j 1 = 0 := by
      funext i
      simp [CharTwo.add_self_eq_zero]
    simp only [swapVec, dotProduct_single_one, Pi.add_apply, Pi.single_apply, hj,
      ite_true, ite_false, zero_add]
    simp only [MulOpposite.op_one, one_smul]
    calc (Pi.single j 1 : Fin n → F) + (Pi.single 0 1 + Pi.single j 1)
        = (Pi.single j 1 + Pi.single j 1) + Pi.single 0 1 := by abel
      _ = Pi.single 0 1 := by rw [h2, zero_add]

theorem swap_conj_radRow {j : Fin n} {g : SpecialLinearGroup (Fin n) F} (hg : g ∈ radRow n F j) :
    swapSL j * g * (swapSL j)⁻¹ ∈ radRow n F 0 := by
  obtain ⟨a, ha, hg⟩ := hg
  have hdot : a ⬝ᵥ swapVec j = 0 := by
    unfold swapVec
    rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one, ha 0 (Fin.zero_le _),
      ha j le_rfl, add_zero]
  have hvec : a ᵥ* (swapMat j : Matrix (Fin n) (Fin n) F) = a := by
    unfold swapMat
    rw [vecMul_add, vecMul_one, vecMul_vecMulVec, hdot, zero_smul, add_zero]
  refine ⟨a, fun i hi => ?_, ?_⟩
  · have hi0 : i = 0 := le_antisymm hi (Fin.zero_le i)
    subst hi0
    exact ha 0 (Fin.zero_le j)
  · rw [swapSL_inv, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hg]
    unfold rowMat
    change swapMat j * _ * swapMat j = _
    rw [conj_one_add_vecMulVec _ _ (swapMat_mul_self j), swapMat_mulVec, hvec]

theorem swapMat_mulVec_zero (j : Fin n) :
    (swapMat j : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single 0 1 : Fin n → F) = Pi.single j 1 := by
  have h := swapMat_mulVec (F := F) j
  have h2 := congrArg (fun x => (swapMat j : Matrix (Fin n) (Fin n) F) *ᵥ x) h
  simp only [mulVec_mulVec, swapMat_mul_self, one_mulVec] at h2
  exact h2.symm

theorem swap_conj_fixPt {j : Fin n} {g : SpecialLinearGroup (Fin n) F}
    (hg : g ∈ fixPt n F (j.val + 1)) : (swapSL j)⁻¹ * g * swapSL j ∈ fixPt n F 1 := by
  intro i hi
  have hi0 : i = 0 := Fin.ext (by simpa using hi)
  subst hi0
  have hgj : (g : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single j 1 : Fin n → F) = Pi.single j 1 :=
    hg j (Nat.lt_succ_self _)
  rw [swapSL_inv, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
    ← mulVec_mulVec]
  change (swapMat j : Matrix (Fin n) (Fin n) F) *ᵥ ((g : Matrix (Fin n) (Fin n) F) *ᵥ
    ((swapMat j : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single 0 1 : Fin n → F))) = _
  rw [swapMat_mulVec_zero, hgj, swapMat_mulVec]

end Swap

end CFSG.CGT.T75N
