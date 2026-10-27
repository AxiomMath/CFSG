module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2

public section

namespace CFSG.Glauberman.Dickson.QuatTable

open BenderSuzuki.MatrixGroups

structure QZ where
  w : ℤ × ℤ
  x : ℤ × ℤ
  y : ℤ × ℤ
  z : ℤ × ℤ

instance : DecidableEq QZ := fun c d =>
  decidable_of_iff (c.w = d.w ∧ c.x = d.x ∧ c.y = d.y ∧ c.z = d.z) (by
    cases c
    cases d
    simp only [QZ.mk.injEq])

@[expose] def tmul (α β : ℤ) (u v : ℤ × ℤ) : ℤ × ℤ :=
  (u.1 * v.1 + β * (u.2 * v.2), u.1 * v.2 + u.2 * v.1 + α * (u.2 * v.2))

@[expose] def qmul (α β : ℤ) (c d : QZ) : QZ where
  w := tmul α β c.w d.w - tmul α β c.x d.x - tmul α β c.y d.y - tmul α β c.z d.z
  x := tmul α β c.w d.x + tmul α β c.x d.w + tmul α β c.y d.z - tmul α β c.z d.y
  y := tmul α β c.w d.y - tmul α β c.x d.z + tmul α β c.y d.w + tmul α β c.z d.x
  z := tmul α β c.w d.z + tmul α β c.x d.y - tmul α β c.y d.x + tmul α β c.z d.w

@[expose] def qsmul (k : ℤ) (c : QZ) : QZ := ⟨k • c.w, k • c.x, k • c.y, k • c.z⟩

@[expose] def qnorm (α β : ℤ) (c : QZ) : ℤ × ℤ :=
  tmul α β c.w c.w + tmul α β c.x c.x + tmul α β c.y c.y + tmul α β c.z c.z

variable {F : Type*} [Field F]

@[expose] def tval (θ : F) (u : ℤ × ℤ) : F := (u.1 : F) + (u.2 : F) * θ

theorem tval_add (θ : F) (u v : ℤ × ℤ) : tval θ (u + v) = tval θ u + tval θ v := by
  simp only [tval, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem tval_sub (θ : F) (u v : ℤ × ℤ) : tval θ (u - v) = tval θ u - tval θ v := by
  simp only [tval, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

theorem tval_smul (θ : F) (k : ℤ) (u : ℤ × ℤ) : tval θ (k • u) = k * tval θ u := by
  simp only [tval, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Int.cast_mul]
  ring

theorem tval_tmul {α β : ℤ} {θ : F} (hθ : θ ^ 2 = α * θ + β) (u v : ℤ × ℤ) :
    tval θ (tmul α β u v) = tval θ u * tval θ v := by
  simp only [tval, tmul, Int.cast_add, Int.cast_mul]
  linear_combination (-((u.2 : F) * (v.2 : F))) * hθ

@[expose] def qmat (a b W X Y Z : F) : Matrix (Fin 2) (Fin 2) F :=
  !![W + Y * a + Z * b, X + Y * b - Z * a; -X + Y * b - Z * a, W - Y * a - Z * b]

theorem qmat_mul {a b : F} (hab : a ^ 2 + b ^ 2 = -1) (W X Y Z W' X' Y' Z' : F) :
    qmat a b W X Y Z * qmat a b W' X' Y' Z' =
      qmat a b (W * W' - X * X' - Y * Y' - Z * Z') (W * X' + X * W' + Y * Z' - Z * Y')
        (W * Y' - X * Z' + Y * W' + Z * X') (W * Z' + X * Y' - Y * X' + Z * W') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [qmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (Y * Y' + Z * Z') * hab
  · linear_combination (-(Y * Z') + Y' * Z) * hab
  · linear_combination (Y * Z' - Y' * Z) * hab
  · linear_combination (Y * Y' + Z * Z') * hab

theorem qmat_det {a b : F} (hab : a ^ 2 + b ^ 2 = -1) (W X Y Z : F) :
    (qmat a b W X Y Z).det = W ^ 2 + X ^ 2 + Y ^ 2 + Z ^ 2 := by
  rw [qmat, Matrix.det_fin_two_of]
  linear_combination (-(Y ^ 2) - Z ^ 2) * hab

theorem qmat_neg (a b W X Y Z : F) :
    qmat a b (-W) (-X) (-Y) (-Z) = -qmat a b W X Y Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmat] <;> ring

theorem qmat_one (a b : F) : qmat a b 1 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmat]

@[expose] def qval (θ a b : F) (c : QZ) : Matrix (Fin 2) (Fin 2) F :=
  qmat a b (tval θ c.w / 2) (tval θ c.x / 2) (tval θ c.y / 2) (tval θ c.z / 2)

variable {α β : ℤ} {θ a b : F}

theorem qval_mul (hθ : θ ^ 2 = α * θ + β) (hab : a ^ 2 + b ^ 2 = -1) (c d : QZ) :
    qval θ a b c * qval θ a b d =
      qmat a b (tval θ (qmul α β c d).w / 2 / 2) (tval θ (qmul α β c d).x / 2 / 2)
        (tval θ (qmul α β c d).y / 2 / 2) (tval θ (qmul α β c d).z / 2 / 2) := by
  rw [qval, qval, qmat_mul hab]
  simp only [qmul, tval_add, tval_sub, tval_tmul hθ]
  congr 1 <;> ring

theorem qval_mul_of_eq (hθ : θ ^ 2 = α * θ + β) (hab : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    {c d e : QZ} {k : ℤ} (hk : k = 2 ∨ k = -2) (h : qmul α β c d = qsmul k e) :
    qval θ a b c * qval θ a b d = qval θ a b e ∨
      qval θ a b c * qval θ a b d = -qval θ a b e := by
  rw [qval_mul hθ hab, h]
  simp only [qsmul, tval_smul]
  rcases hk with rfl | rfl
  · left
    rw [qval]
    congr 1 <;> field_simp <;> push_cast <;> ring
  · right
    rw [qval, ← qmat_neg]
    congr 1 <;> field_simp <;> push_cast <;> ring

theorem qval_det (hθ : θ ^ 2 = α * θ + β) (hab : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    {c : QZ} (hc : qnorm α β c = (4, 0)) : (qval θ a b c).det = 1 := by
  have h := congrArg (tval θ) hc
  simp only [qnorm, tval_add, tval_tmul hθ] at h
  rw [qval, qmat_det hab]
  have h4 : tval θ ((4 : ℤ), (0 : ℤ)) = 4 := by simp [tval]
  rw [h4] at h
  field_simp
  linear_combination h

theorem neg_one_mem_center_SL :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg]

theorem mk_neg_SL (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) (-A) :
      PSL2MatrixGroup F) = QuotientGroup.mk' _ A := by
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨-1, neg_one_mem_center_SL, ?_⟩
  rw [mul_neg, mul_one, neg_neg]

theorem exists_psl2Hom_of_table (hθ : θ ^ 2 = α * θ + β) (hab : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) {G : Type*} [Group G] (T : G → QZ) (gens : List G)
    (hgen : Subgroup.closure {x | x ∈ gens} = ⊤)
    (hnorm : ∀ g, qnorm α β (T g) = (4, 0))
    (hone : T 1 = ⟨(2, 0), (0, 0), (0, 0), (0, 0)⟩)
    (hmul : ∀ g, ∀ s ∈ gens, qmul α β (T g) (T s) = qsmul 2 (T (g * s)) ∨
      qmul α β (T g) (T s) = qsmul (-2) (T (g * s))) :
    ∃ φ : G →* PSL2MatrixGroup F, ∀ g, ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F) = qval θ a b (T g) ∧ φ g = QuotientGroup.mk' _ A := by
  let A : G → Matrix.SpecialLinearGroup (Fin 2) F := fun g =>
    ⟨qval θ a b (T g), qval_det hθ hab h2 (hnorm g)⟩
  let π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  let f : G → PSL2MatrixGroup F := fun g => π (A g)
  have hA1 : A 1 = 1 := by
    apply Subtype.ext
    change qval θ a b (T 1) = 1
    rw [hone, qval]
    have h0 : tval θ ((0 : ℤ), (0 : ℤ)) / 2 = 0 := by simp [tval]
    have h1 : tval θ ((2 : ℤ), (0 : ℤ)) / 2 = 1 := by
      simp only [tval, Int.cast_ofNat, Int.cast_zero, zero_mul, add_zero]
      field_simp
    rw [h0, h1, qmat_one]
  have hf1 : f 1 = 1 := by
    change π (A 1) = 1
    rw [hA1, map_one]
  have hfs : ∀ g, ∀ s ∈ gens, f (g * s) = f g * f s := by
    intro g s hs
    change π (A (g * s)) = π (A g) * π (A s)
    rw [← map_mul]
    have hk : (2 : ℤ) = 2 ∨ (2 : ℤ) = -2 := Or.inl rfl
    have hk' : (-2 : ℤ) = 2 ∨ (-2 : ℤ) = -2 := Or.inr rfl
    rcases hmul g s hs with h | h
    · rcases qval_mul_of_eq hθ hab h2 hk h with h' | h'
      · congr 1
        exact Subtype.ext h'.symm
      · rw [← mk_neg_SL (A g * A s)]
        congr 1
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_mul]
        change qval θ a b (T (g * s)) = -(qval θ a b (T g) * qval θ a b (T s))
        rw [h', neg_neg]
    · rcases qval_mul_of_eq hθ hab h2 hk' h with h' | h'
      · congr 1
        exact Subtype.ext h'.symm
      · rw [← mk_neg_SL (A g * A s)]
        congr 1
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_mul]
        change qval θ a b (T (g * s)) = -(qval θ a b (T g) * qval θ a b (T s))
        rw [h', neg_neg]
  let S : Subgroup G :=
    { carrier := {h | ∀ g, f (g * h) = f g * f h}
      one_mem' := by
        intro g
        rw [mul_one, hf1, mul_one]
      mul_mem' := by
        intro h₁ h₂ hh₁ hh₂ g
        rw [← mul_assoc, hh₂, hh₁, hh₂ h₁, mul_assoc]
      inv_mem' := by
        intro h hh g
        have h1 := hh (g * h⁻¹)
        have h2' := hh h⁻¹
        rw [inv_mul_cancel_right] at h1
        rw [inv_mul_cancel, hf1] at h2'
        have hinv : f h⁻¹ = (f h)⁻¹ := eq_inv_of_mul_eq_one_left h2'.symm
        rw [hinv, eq_mul_inv_iff_mul_eq]
        exact h1.symm }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro s hs g
    exact hfs g s hs
  let φ : G →* PSL2MatrixGroup F :=
    { toFun := f
      map_one' := hf1
      map_mul' := fun g h => by
        have hh : h ∈ S := hS ▸ Subgroup.mem_top h
        exact hh g }
  exact ⟨φ, fun g => ⟨A g, rfl, rfl⟩⟩

end CFSG.Glauberman.Dickson.QuatTable
