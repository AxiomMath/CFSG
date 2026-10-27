module

public import CFSG.ClassicalInvolution.WeakCT.Amalgam
public import CFSG.ClassicalInvolution.RouteD.GapsPerfect
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.WeakCT CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F]

theorem coe_transvection_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : F) :
    ((Matrix.SpecialLinearGroup.transvection hij c : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      1 + Matrix.single i j c := by
  rw [Matrix.SpecialLinearGroup.transvection_coe]

theorem transvection_inv_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : F) :
    (Matrix.SpecialLinearGroup.transvection hij c : SL(n, F))⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (-c) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  have h0 : Matrix.single i j c * Matrix.single i j (-c) = 0 :=
    Matrix.single_mul_single_of_ne c i j i hij.symm (-c)
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_transvection_eq, coe_transvection_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h0, add_zero]
  rw [add_assoc 1, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]
  rfl

theorem coe_transvection_inv_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : F) :
    (((Matrix.SpecialLinearGroup.transvection hij c : SL(n, F))⁻¹ : SL(n, F)) :
      Matrix (Fin n) (Fin n) F) = 1 + Matrix.single i j (-c) := by
  rw [transvection_inv_eq, coe_transvection_eq]

@[expose] noncomputable def diagGL {n : ℕ} (d : Fin n → Fˣ) : GL (Fin n) F where
  val := Matrix.diagonal fun i => (d i : F)
  inv := Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp

theorem coe_diagGL {n : ℕ} (d : Fin n → Fˣ) :
    ((diagGL d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.diagonal fun i => (d i : F) :=
  rfl

theorem coe_diagGL_inv {n : ℕ} (d : Fin n → Fˣ) :
    (((diagGL d)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F) :=
  rfl

theorem slConjugation_diagGL_apply {n : ℕ} (d : Fin n → Fˣ) (x : SL(n, F)) (i j : Fin n) :
    ((slConjugation n F (diagGL d) x : SL(n, F)) : Matrix (Fin n) (Fin n) F) i j =
      (d i : F) * (x : Matrix (Fin n) (Fin n) F) i j * (((d j)⁻¹ : Fˣ) : F) := by
  rw [slConjugation_matrix, coe_diagGL, coe_diagGL_inv, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem hom_eq_of_central_ker {n : ℕ} {X : Type*} [Group X] (θ : SL(n, F) →* X)
    (hker : θ.ker ≤ Subgroup.center SL(n, F)) {L : Type*} [Group L] [Group.IsPerfect L]
    (f h : L →* SL(n, F)) (hfh : ∀ l, θ (f l) = θ (h l)) : f = h := by
  have hmem : ∀ l, (h l)⁻¹ * f l ∈ Subgroup.center SL(n, F) := fun l => by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfh l, inv_mul_cancel]
  let z : L →* Subgroup.center SL(n, F) :=
    { toFun := fun l => ⟨(h l)⁻¹ * f l, hmem l⟩
      map_one' := by simp
      map_mul' := fun l₁ l₂ => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hmem l₁)
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        calc (h l₂)⁻¹ * (h l₁)⁻¹ * (f l₁ * f l₂)
            = (h l₂)⁻¹ * ((h l₁)⁻¹ * f l₁) * f l₂ := by group
          _ = ((h l₁)⁻¹ * f l₁) * (h l₂)⁻¹ * f l₂ := by rw [hc ((h l₂)⁻¹)]
          _ = ((h l₁)⁻¹ * f l₁) * ((h l₂)⁻¹ * f l₂) := by group }
  have hz : z = 1 := hom_eq_one_of_perfect_of_solvable z
  refine MonoidHom.ext fun l => ?_
  have := congrArg (fun w : Subgroup.center SL(n, F) => (w : SL(n, F))) (DFunLike.congr_fun hz l)
  simp only [MonoidHom.one_apply, z, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at this
  exact inv_mul_eq_one.mp this |>.symm

theorem block_of_commute_single {n : ℕ} (g : Matrix (Fin n) (Fin n) F) {a b : Fin n}
    (h1 : g * Matrix.single a b (1 : F) = Matrix.single a b 1 * g)
    (h2 : g * Matrix.single b a (1 : F) = Matrix.single b a 1 * g) :
    g a a = g b b ∧ (∀ i, i ≠ a → g i a = 0) ∧ (∀ i, i ≠ b → g i b = 0) ∧
      (∀ j, j ≠ a → g a j = 0) ∧ (∀ j, j ≠ b → g b j = 0) := by
  have c1 : ∀ i, g i a = (Matrix.single a b (1 : F) * g) i b := fun i => by
    have := congrFun (congrFun h1 i) b
    rw [Matrix.mul_single_apply_same, mul_one] at this
    exact this
  have c2 : ∀ i, g i b = (Matrix.single b a (1 : F) * g) i a := fun i => by
    have := congrFun (congrFun h2 i) a
    rw [Matrix.mul_single_apply_same, mul_one] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := c1 a
    rw [Matrix.single_mul_apply_same, one_mul] at this
    exact this
  · intro i hi
    rw [c1 i, Matrix.single_mul_apply_of_ne (c := (1 : F)) (i := a) (j := b) (a := i) (b := b) hi]
  · intro i hi
    rw [c2 i, Matrix.single_mul_apply_of_ne (c := (1 : F)) (i := b) (j := a) (a := i) (b := a) hi]
  · intro j hj
    have := congrFun (congrFun h2 b) j
    rw [Matrix.mul_single_apply_of_ne (c := (1 : F)) (i := b) (j := a) (a := b) (b := j) hj,
      Matrix.single_mul_apply_same, one_mul] at this
    exact this.symm
  · intro j hj
    have := congrFun (congrFun h1 a) j
    rw [Matrix.mul_single_apply_of_ne (c := (1 : F)) (i := a) (j := b) (a := a) (b := j) hj,
      Matrix.single_mul_apply_same, one_mul] at this
    exact this.symm

theorem mul_eq_of_conj_eq {n : ℕ} (g : GL (Fin n) F) {M N : Matrix (Fin n) (Fin n) F}
    (h : (g : Matrix (Fin n) (Fin n) F) * M * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = N) :
    (g : Matrix (Fin n) (Fin n) F) * M = N * (g : Matrix (Fin n) (Fin n) F) := by
  have hinv : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) = 1 :=
    Units.inv_mul g
  calc (g : Matrix (Fin n) (Fin n) F) * M
      = (g : Matrix (Fin n) (Fin n) F) * M * (((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F)) := by
        rw [hinv, Matrix.mul_one]
    _ = ((g : Matrix (Fin n) (Fin n) F) * M * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (g : Matrix (Fin n) (Fin n) F) := by
        simp only [Matrix.mul_assoc]
    _ = N * (g : Matrix (Fin n) (Fin n) F) := by rw [h]

theorem conj_eq_of_mul_eq {n : ℕ} (g : GL (Fin n) F) {M N : Matrix (Fin n) (Fin n) F}
    (h : (g : Matrix (Fin n) (Fin n) F) * M = N * (g : Matrix (Fin n) (Fin n) F)) :
    (g : Matrix (Fin n) (Fin n) F) * M * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = N := by
  rw [h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem commute_single_of_conj_fixed {n : ℕ} (g : GL (Fin n) F) {i j : Fin n} (hij : i ≠ j)
    (h : slConjugation n F g (Matrix.SpecialLinearGroup.transvection hij (1 : F)) =
      Matrix.SpecialLinearGroup.transvection hij (1 : F)) :
    (g : Matrix (Fin n) (Fin n) F) * Matrix.single i j (1 : F) =
      Matrix.single i j (1 : F) * (g : Matrix (Fin n) (Fin n) F) := by
  have h1 := congrArg (fun x : SL(n, F) => (x : Matrix (Fin n) (Fin n) F)) h
  simp only [slConjugation_matrix, coe_transvection_eq] at h1
  have h2 := mul_eq_of_conj_eq g h1
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h2
  exact add_left_cancel h2

theorem commute_of_fixes_block {m : ℕ} (g : GL (Fin (m + 1)) F) (a : Fin m)
    (h : ∀ A : SL(2, F), slConjugation (m + 1) F g (blockSL2 F m a A) = blockSL2 F m a A) :
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.single a.castSucc a.succ (1 : F) =
        Matrix.single a.castSucc a.succ (1 : F) * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.single a.succ a.castSucc (1 : F) =
        Matrix.single a.succ a.castSucc (1 : F) * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  constructor
  · apply commute_single_of_conj_fixed g (Fin.castSucc_lt_succ.ne)
    have := h (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1)
    rwa [blockSL2_transvection_up] at this
  · apply commute_single_of_conj_fixed g (Fin.castSucc_lt_succ.ne')
    have := h (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1)
    rwa [blockSL2_transvection_down] at this

theorem exists_diagGL_of_offdiag_zero {n : ℕ} (g : GL (Fin n) F)
    (h : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    ∃ u : Fin n → Fˣ, g = diagGL u := by
  have hne : ∀ i, (g : Matrix (Fin n) (Fin n) F) i i ≠ 0 := fun i hi => by
    have h1 := congrFun (congrFun (Units.mul_inv g) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [h i k hk.symm, zero_mul])
      (fun hi' => absurd (Finset.mem_univ i) hi'), hi, zero_mul] at h1
    simp at h1
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_diagGL, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, h i j hij]

theorem slConjugation_diagGL_blockSL2 {m : ℕ} (d : Fin (m + 1) → Fˣ) (a : Fin m)
    (hd : d a.castSucc = d a.succ) (A : SL(2, F)) :
    slConjugation (m + 1) F (diagGL d) (blockSL2 F m a A) = blockSL2 F m a A := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply]
  have hblock : ∀ i : Fin (m + 1), (a.val ≤ i.val ∧ i.val < a.val + 2) → d i = d a.castSucc := by
    intro i hi
    by_cases h0 : i.val = a.val
    · rw [show i = a.castSucc from Fin.ext h0]
    · rw [show i = a.succ from Fin.ext (by simp only [Fin.val_succ]; omega), ← hd]
  have hmat : ((blockSL2 F m a A : SL(m + 1, F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
      if h : (a.val ≤ i.val ∧ i.val < a.val + 2) ∧ (a.val ≤ j.val ∧ j.val < a.val + 2) then
        (A : Matrix (Fin 2) (Fin 2) F) ⟨i.val - a.val, by omega⟩ ⟨j.val - a.val, by omega⟩
      else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j :=
    CFSG.ClassicalInvolution.Phan.blockMat_apply _ i j
  rw [hmat]
  by_cases h : (a.val ≤ i.val ∧ i.val < a.val + 2) ∧ (a.val ≤ j.val ∧ j.val < a.val + 2)
  · rw [dite_eq_left h, hblock i h.1, hblock j h.2, mul_right_comm, Units.mul_inv, one_mul]
  · rw [dite_eq_right h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

theorem diag_eq_of_conj_fixed {n : ℕ} (d : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j)
    (h : slConjugation n F (diagGL d) (Matrix.SpecialLinearGroup.transvection hij (1 : F)) =
      Matrix.SpecialLinearGroup.transvection hij (1 : F)) : d i = d j := by
  have h1 := congrFun (congrFun (congrArg (fun x : SL(n, F) => (x : Matrix (Fin n) (Fin n) F)) h) i) j
  rw [slConjugation_diagGL_apply, coe_transvection_eq] at h1
  simp [Matrix.add_apply, hij] at h1
  have h2 : (d i : F) = d j := by
    have hj : (d j : F) ≠ 0 := (d j).ne_zero
    field_simp at h1
    exact h1
  exact Units.ext h2

theorem slConjugation_diagGL_congr {n : ℕ} (u v : Fin n → Fˣ) (c : Fˣ)
    (h : ∀ i, u i = c * v i) (x : SL(n, F)) :
    slConjugation n F (diagGL u) x = slConjugation n F (diagGL v) x := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply, slConjugation_diagGL_apply, h i, h j]
  have hc : (c : F) ≠ 0 := c.ne_zero
  have hvi : (v i : F) ≠ 0 := (v i).ne_zero
  have hvj : (v j : F) ≠ 0 := (v j).ne_zero
  simp only [Units.val_mul, mul_inv_rev, Units.val_inv_eq_inv_val]
  field_simp

theorem sq_eq_of_conj_sq {n : ℕ} (u : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j)
    (h : ∀ x : SL(n, F), slConjugation n F (diagGL u) (slConjugation n F (diagGL u) x) = x) :
    (u i : F) ^ 2 = (u j : F) ^ 2 := by
  have h1 := congrFun (congrFun (congrArg (fun x : SL(n, F) => (x : Matrix (Fin n) (Fin n) F))
    (h (Matrix.SpecialLinearGroup.transvection hij (1 : F)))) i) j
  rw [slConjugation_diagGL_apply, slConjugation_diagGL_apply, coe_transvection_eq] at h1
  simp [Matrix.add_apply, hij] at h1
  have hj : (u j : F) ≠ 0 := (u j).ne_zero
  field_simp at h1
  linear_combination h1

theorem mapMatrix_one_add_single {n : ℕ} (φ : F ≃+* F) (i j : Fin n) (c : F) :
    φ.mapMatrix (1 + Matrix.single i j c) = 1 + Matrix.single i j (φ c) := by
  rw [map_add, map_one]
  congr 1
  ext a b
  rw [RingEquiv.mapMatrix_apply, Matrix.map_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

theorem block_of_graph_commute {n : ℕ} (g : Matrix (Fin n) (Fin n) F) {i j : Fin n}
    (h1 : g * Matrix.single j i (-1 : F) = Matrix.single i j 1 * g)
    (h2 : g * Matrix.single i j (-1 : F) = Matrix.single j i 1 * g) :
    (∀ k, k ≠ i → g k j = 0) ∧ (∀ l, l ≠ i → g j l = 0) ∧ (∀ k, k ≠ j → g k i = 0) ∧
      (∀ l, l ≠ j → g i l = 0) ∧ g i j = - g j i := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have := congrFun (congrFun h1 k) i
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (c := (1 : F)) (i := i)
      (j := j) (a := k) (b := i) hk] at this
    simpa using this
  · intro l hl
    have := congrFun (congrFun h1 i) l
    rw [Matrix.mul_single_apply_of_ne (c := (-1 : F)) (i := j) (j := i) (a := i) (b := l) hl,
      Matrix.single_mul_apply_same, one_mul] at this
    exact this.symm
  · intro k hk
    have := congrFun (congrFun h2 k) j
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (c := (1 : F)) (i := j)
      (j := i) (a := k) (b := j) hk] at this
    simpa using this
  · intro l hl
    have := congrFun (congrFun h2 j) l
    rw [Matrix.mul_single_apply_of_ne (c := (-1 : F)) (i := i) (j := j) (a := j) (b := l) hl,
      Matrix.single_mul_apply_same, one_mul] at this
    exact this.symm
  · have := congrFun (congrFun h1 i) i
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, one_mul] at this
    linear_combination -this

theorem conj_single {n : ℕ} (g : GL (Fin n) F) (p q : Fin n) (r : F) :
    (g : Matrix (Fin n) (Fin n) F) * Matrix.single p q r * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      r • ((g : Matrix (Fin n) (Fin n) F) * Matrix.single p q (1 : F) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  have : Matrix.single p q r = r • Matrix.single p q (1 : F) := by
    ext a b; simp [Matrix.single_apply]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_one_add {n : ℕ} (g : GL (Fin n) F) (N : Matrix (Fin n) (Fin n) F) :
    (g : Matrix (Fin n) (Fin n) F) * (1 + N) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + (g : Matrix (Fin n) (Fin n) F) * N * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv]

theorem fixed_transvection_false {n : ℕ} (α : SL(n, F) →* SL(n, F)) (g : GL (Fin n) F)
    (φ : F ≃+* F)
    (hα : ∀ x, ((α x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) * φ.mapMatrix (x : Matrix (Fin n) (Fin n) F) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    {i j : Fin n} (hij : i ≠ j)
    (hup : ∀ c : F, α (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij c) :
    (∀ c, φ c = c) ∧ (g : Matrix (Fin n) (Fin n) F) * Matrix.single i j (1 : F) =
      Matrix.single i j (1 : F) * (g : Matrix (Fin n) (Fin n) F) := by
  have key : ∀ c : F, (g : Matrix (Fin n) (Fin n) F) * Matrix.single i j (φ c) *
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.single i j c := by
    intro c
    have h := congrArg (fun x : SL(n, F) => (x : Matrix (Fin n) (Fin n) F)) (hup c)
    simp only [hα, coe_transvection_eq, mapMatrix_one_add_single, conj_one_add] at h
    exact add_left_cancel h
  have h1 : (g : Matrix (Fin n) (Fin n) F) * Matrix.single i j (1 : F) *
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.single i j (1 : F) := by
    simpa using key 1
  refine ⟨fun c => ?_, mul_eq_of_conj_eq g h1⟩
  have h2 := key c
  rw [conj_single, h1] at h2
  have h3 := congrFun (congrFun h2 i) j
  simpa using h3

theorem fixed_transvection_true {n : ℕ} (α : SL(n, F) →* SL(n, F)) (g : GL (Fin n) F)
    (φ : F ≃+* F)
    (hα : ∀ x, ((α x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) *
        φ.mapMatrix (((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F))ᵀ *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    {i j : Fin n} (hij : i ≠ j)
    (hup : ∀ c : F, α (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij c) :
    (∀ c, φ c = c) ∧ (g : Matrix (Fin n) (Fin n) F) * Matrix.single j i (-1 : F) =
      Matrix.single i j (1 : F) * (g : Matrix (Fin n) (Fin n) F) := by
  have hT : ∀ c : F, φ.mapMatrix ((((Matrix.SpecialLinearGroup.transvection hij c)⁻¹ : SL(n, F)) :
      Matrix (Fin n) (Fin n) F))ᵀ = 1 + Matrix.single j i (-φ c) := by
    intro c
    rw [coe_transvection_inv_eq, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single, mapMatrix_one_add_single, map_neg]
  have key : ∀ c : F, (g : Matrix (Fin n) (Fin n) F) * Matrix.single j i (-φ c) *
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.single i j c := by
    intro c
    have h := congrArg (fun x : SL(n, F) => (x : Matrix (Fin n) (Fin n) F)) (hup c)
    simp only [hα, coe_transvection_eq, hT, conj_one_add] at h
    exact add_left_cancel h
  have h1 : (g : Matrix (Fin n) (Fin n) F) * Matrix.single j i (-1 : F) *
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.single i j (1 : F) := by
    simpa using key 1
  refine ⟨fun c => ?_, mul_eq_of_conj_eq g h1⟩
  have h2 := key c
  rw [conj_single] at h2
  rw [conj_single] at h1
  have hM : (g : Matrix (Fin n) (Fin n) F) * Matrix.single j i (1 : F) *
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = -Matrix.single i j (1 : F) := by
    rw [← h1, neg_one_smul, neg_neg]
  rw [hM, smul_neg, ← neg_smul, neg_neg] at h2
  have h3 := congrFun (congrFun h2 i) j
  simpa using h3

theorem exists_smul_one_of_commute_single {n : ℕ} (h : Matrix (Fin n) (Fin n) F) (hn : 1 ≤ n)
    (hc : ∀ i j : Fin n, i ≠ j → h * Matrix.single i j (1 : F) = Matrix.single i j (1 : F) * h) :
    ∃ c : F, h = c • (1 : Matrix (Fin n) (Fin n) F) := by
  have hd : ∀ i j, i ≠ j → h i j = 0 := fun i j hij =>
    (block_of_commute_single h (hc j i hij.symm) (hc i j hij)).2.1 i hij
  have he : ∀ i j, h i i = h j j := fun i j => by
    by_cases hij : i = j
    · rw [hij]
    · exact (block_of_commute_single h (hc i j hij) (hc j i (Ne.symm hij))).1
  refine ⟨h ⟨0, hn⟩ ⟨0, hn⟩, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab; simp [he a ⟨0, hn⟩]
  · simp [hab, hd a b hab]

theorem exists_eq_smul_transpose {n : ℕ} (hn : 2 ≤ n) (α : SL(n, F) →* SL(n, F))
    (g : GL (Fin n) F)
    (hα : ∀ x, ((α x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) * (((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F))ᵀ *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hsq : ∀ x, α (α x) = x) :
    ∃ c : F, (g : Matrix (Fin n) (Fin n) F) = c • (g : Matrix (Fin n) (Fin n) F)ᵀ := by
  set G : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) with hG
  set Gi : Matrix (Fin n) (Fin n) F := ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hGi
  have hGGi : G * Gi = 1 := Units.mul_inv g
  have hGiG : Gi * G = 1 := Units.inv_mul g
  have hT1 : Gi.transpose * G.transpose = 1 := by
    rw [← Matrix.transpose_mul, hGGi, Matrix.transpose_one]
  have hT2 : G.transpose * Gi.transpose = 1 := by
    rw [← Matrix.transpose_mul, hGiG, Matrix.transpose_one]
  have hx : ∀ x : SL(n, F), (x : Matrix (Fin n) (Fin n) F) =
      (G * Gi.transpose) * (x : Matrix (Fin n) (Fin n) F) * (G.transpose * Gi) := by
    intro x
    have h1 := congrArg (fun y : SL(n, F) => (y : Matrix (Fin n) (Fin n) F)) (hsq x)
    rw [hα (α x), ← map_inv, hα (x⁻¹), inv_inv, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose] at h1
    exact h1.symm.trans (by simp only [Matrix.mul_assoc])
  set H : Matrix (Fin n) (Fin n) F := G * Gi.transpose with hH
  have hK : (G.transpose * Gi) * H = 1 := by
    rw [hH, Matrix.mul_assoc, ← Matrix.mul_assoc Gi, hGiG, Matrix.one_mul, hT2]
  have hcomm : ∀ x : SL(n, F), H * (x : Matrix (Fin n) (Fin n) F) =
      (x : Matrix (Fin n) (Fin n) F) * H := by
    intro x
    have h2 := congrArg (fun y => y * H) (hx x)
    rw [Matrix.mul_assoc (H * (x : Matrix (Fin n) (Fin n) F)), hK, Matrix.mul_one] at h2
    exact h2.symm
  have hcs : ∀ i j : Fin n, i ≠ j → H * Matrix.single i j (1 : F) = Matrix.single i j (1 : F) * H := by
    intro i j hij
    have h3 := hcomm (Matrix.SpecialLinearGroup.transvection hij (1 : F))
    rw [coe_transvection_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h3
    exact add_left_cancel h3
  obtain ⟨c, hc⟩ := exists_smul_one_of_commute_single H (by omega) hcs
  refine ⟨c, ?_⟩
  calc G = G * (Gi.transpose * G.transpose) := by rw [hT1, Matrix.mul_one]
    _ = H * G.transpose := by rw [hH, Matrix.mul_assoc]
    _ = c • G.transpose := by rw [hc, Matrix.smul_mul, Matrix.one_mul]

theorem det_ne_zero_of_gl {n : ℕ} (g : GL (Fin n) F) :
    (g : Matrix (Fin n) (Fin n) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin n) (Fin n) F)).mp g.isUnit).ne_zero

theorem eq_neg_transpose_of_graph_block {n : ℕ} (g : GL (Fin n) F) {i j : Fin n} (c : F)
    (hgc : (g : Matrix (Fin n) (Fin n) F) = c • (g : Matrix (Fin n) (Fin n) F)ᵀ)
    (hcol : ∀ k, k ≠ j → (g : Matrix (Fin n) (Fin n) F) k i = 0)
    (hij : (g : Matrix (Fin n) (Fin n) F) i j = -(g : Matrix (Fin n) (Fin n) F) j i) :
    (g : Matrix (Fin n) (Fin n) F) = -(g : Matrix (Fin n) (Fin n) F)ᵀ := by
  have hji : (g : Matrix (Fin n) (Fin n) F) j i ≠ 0 := by
    intro h0
    apply det_ne_zero_of_gl g
    refine Matrix.det_eq_zero_of_column_eq_zero i fun k => ?_
    by_cases hk : k = j
    · rw [hk]; exact h0
    · exact hcol k hk
  have hc : c = -1 := by
    have h1 := congrFun (congrFun hgc i) j
    rw [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hij] at h1
    have h2 : (c + 1) * (g : Matrix (Fin n) (Fin n) F) j i = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linear_combination h3
    · exact absurd h3 hji
  calc (g : Matrix (Fin n) (Fin n) F) = c • (g : Matrix (Fin n) (Fin n) F)ᵀ := hgc
    _ = (-1 : F) • (g : Matrix (Fin n) (Fin n) F)ᵀ := by rw [hc]
    _ = -(g : Matrix (Fin n) (Fin n) F)ᵀ := neg_one_smul _ _

theorem skew_block_identity (G : Matrix (Fin 4) (Fin 4) F)
    (z02 : G 0 2 = 0) (z03 : G 0 3 = 0) (z12 : G 1 2 = 0) (z13 : G 1 3 = 0)
    (z20 : G 2 0 = 0) (z21 : G 2 1 = 0) (z30 : G 3 0 = 0) (z31 : G 3 1 = 0)
    (h00 : G 0 0 = 0) (h11 : G 1 1 = 0) (h10 : G 1 0 = -G 0 1) (A : SL(2, F)) :
    G * (blockMat 4 0 ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))ᵀ =
      blockMat 4 0 (A : Matrix (Fin 2) (Fin 2) F) * G := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, blockMat_apply, Matrix.transpose_apply, h00, h11,
      h10, z02, z03, z12, z13, z20, z21, z30, z31] <;> ring

theorem exists_diagonalizer_two (h2 : (2 : F) ≠ 0) (lam : F) (hlam : lam ≠ 0)
    (U : Matrix (Fin 2) (Fin 2) F) (hU : U * U = (lam * lam) • (1 : Matrix (Fin 2) (Fin 2) F))
    (h1 : U ≠ lam • 1) (h3 : U ≠ (-lam) • 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧
      U * P = P * Matrix.diagonal ![-lam, lam] := by
  set Nm : Matrix (Fin 2) (Fin 2) F := U - lam • 1 with hNm
  set Np : Matrix (Fin 2) (Fin 2) F := U + lam • 1 with hNp
  have eNm : U * Nm = (-lam) • Nm := by
    rw [hNm, Matrix.mul_sub, hU, Matrix.mul_smul, Matrix.mul_one]
    module
  have eNp : U * Np = lam • Np := by
    rw [hNp, Matrix.mul_add, hU, Matrix.mul_smul, Matrix.mul_one]
    module
  have hnz : ∀ N : Matrix (Fin 2) (Fin 2) F, N ≠ 0 → ∃ j, ∃ i, N i j ≠ 0 := by
    intro N hN
    by_contra hcon
    push Not at hcon
    exact hN (by ext i j; exact hcon j i)
  obtain ⟨j₁, i₁, hi₁⟩ := hnz Nm (sub_ne_zero.mpr h1)
  obtain ⟨j₂, i₂, hi₂⟩ := hnz Np (by
    intro h
    apply h3
    have : U = -(lam • 1) := by rw [hNp] at h; exact eq_neg_of_add_eq_zero_left h
    rw [this, neg_smul])
  set P : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => if j = 0 then Nm i j₁ else Np i j₂
    with hP
  have hUP : U * P = P * Matrix.diagonal ![-lam, lam] := by
    ext i j
    fin_cases j
    · have := congrFun (congrFun eNm i) j₁
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
      simp only [hP, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two] at this ⊢
      simp [this]
      ring
    · have := congrFun (congrFun eNp i) j₂
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
      simp only [hP, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two] at this ⊢
      simp [this]
      ring
  refine ⟨P, ?_, hUP⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hPv : ∀ i, Nm i j₁ * v 0 + Np i j₂ * v 1 = 0 := fun i => by
    have := congrFun hv i
    simpa [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hPv' : ∀ i, Nm i j₁ * (-lam * v 0) + Np i j₂ * (lam * v 1) = 0 := fun i => by
    have h4 : (U * P) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [hUP, ← Matrix.mulVec_mulVec] at h4
    have := congrFun h4 i
    simpa [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.diagonal_apply] using this
  have hv1 : v 1 = 0 := by
    have : Np i₂ j₂ * (2 * lam * v 1) = 0 := by
      linear_combination hPv' i₂ + lam * hPv i₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hi₂
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' h2
        · exact absurd h'' hlam
      · exact h'
  have hv0' : v 0 = 0 := by
    have : Nm i₁ j₁ * (2 * lam * v 0) = 0 := by
      linear_combination lam * hPv i₁ - hPv' i₁
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hi₁
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' h2
        · exact absurd h'' hlam
      · exact h'
  apply hv0
  ext k
  fin_cases k <;> simp [hv1, hv0']

theorem block_conj_identity (G : Matrix (Fin 4) (Fin 4) F) (lam : F) (P : Matrix (Fin 2) (Fin 2) F)
    (z02 : G 0 2 = 0) (z03 : G 0 3 = 0) (z12 : G 1 2 = 0) (z13 : G 1 3 = 0)
    (z20 : G 2 0 = 0) (z21 : G 2 1 = 0) (z30 : G 3 0 = 0) (z31 : G 3 1 = 0)
    (z23 : G 2 3 = 0) (z32 : G 3 2 = 0) (h22 : G 2 2 = lam) (h33 : G 3 3 = lam)
    (e00 : G 0 0 * P 0 0 + G 0 1 * P 1 0 = P 0 0 * -lam)
    (e01 : G 0 0 * P 0 1 + G 0 1 * P 1 1 = P 0 1 * lam)
    (e10 : G 1 0 * P 0 0 + G 1 1 * P 1 0 = P 1 0 * -lam)
    (e11 : G 1 0 * P 0 1 + G 1 1 * P 1 1 = P 1 1 * lam) :
    G * blockMat 4 0 P = blockMat 4 0 P * Matrix.diagonal ![-lam, lam, lam, lam] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, blockMat_apply, Matrix.diagonal_apply, z02, z03, z12,
      z13, z20, z21, z30, z31, z23, z32, h22, h33, e00, e01, e10, e11]

end CFSG.ClassicalInvolution.RouteD.Gaps
