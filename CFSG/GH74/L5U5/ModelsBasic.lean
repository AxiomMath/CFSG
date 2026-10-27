module

public import CFSG.GH74.Filter.ClassicalOdd.Unitary
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.GH74.L5U5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.Filter.ClassicalOdd

section Blocks

variable {F : Type} [Field F]

abbrev e4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv (m := 2) (n := 2)

abbrev blk4 (X Y : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  diagBlock (k := 2) (m := 2) X Y

theorem blk4_eq_reindex (X Y : Matrix (Fin 2) (Fin 2) F) :
    blk4 X Y = Matrix.reindexAlgEquiv F F e4 (fromBlocks X 0 0 Y) := by
  rw [Matrix.coe_reindexAlgEquiv]; rfl

theorem blk4_mul (X X' Y Y' : Matrix (Fin 2) (Fin 2) F) :
    blk4 X Y * blk4 X' Y' = blk4 (X * X') (Y * Y') := diagBlock_mul X X' Y Y'

theorem blk4_one : blk4 (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := diagBlock_one

theorem det_blk4 (X Y : Matrix (Fin 2) (Fin 2) F) : (blk4 X Y).det = X.det * Y.det :=
  det_diagBlock X Y

theorem blk4_neg (A B : Matrix (Fin 2) (Fin 2) F) : blk4 (-A) (-B) = - blk4 A B := by
  have h : fromBlocks (-A) 0 0 (-B) = -fromBlocks A 0 0 B := by rw [fromBlocks_neg, neg_zero]
  rw [blk4_eq_reindex, blk4_eq_reindex, h, map_neg]

theorem blk4_inj {X Y X' Y' : Matrix (Fin 2) (Fin 2) F} (h : blk4 X Y = blk4 X' Y') :
    X = X' ∧ Y = Y' := by
  rw [blk4_eq_reindex, blk4_eq_reindex] at h
  have h' := (Matrix.reindexAlgEquiv F F e4).injective h
  have := (fromBlocks_inj.1 h')
  exact ⟨this.1, this.2.2.2⟩

@[expose] def wMat : Matrix (Fin 4) (Fin 4) F :=
  Matrix.reindexAlgEquiv F F e4 (fromBlocks 0 1 1 0)

theorem wMat_mul_self : (wMat : Matrix (Fin 4) (Fin 4) F) * wMat = 1 := by
  rw [wMat, ← map_mul]
  have : (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      fromBlocks 0 1 1 0 = 1 := by
    rw [fromBlocks_multiply]; simp [fromBlocks_one]
  rw [this, map_one]

theorem wMat_mul_blk4_mul_wMat (A B : Matrix (Fin 2) (Fin 2) F) :
    (wMat : Matrix (Fin 4) (Fin 4) F) * blk4 A B * wMat = blk4 B A := by
  rw [wMat, blk4_eq_reindex, blk4_eq_reindex, ← map_mul, ← map_mul]
  congr 1
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp

end Blocks

section DiagGL

variable {F : Type} [Field F]

@[expose] def diagGL (a b : GL (Fin 2) F) : GL (Fin 4) F where
  val := blk4 (a : Matrix (Fin 2) (Fin 2) F) (b : Matrix (Fin 2) (Fin 2) F)
  inv := blk4 (a⁻¹ : GL (Fin 2) F) (b⁻¹ : GL (Fin 2) F)
  val_inv := by rw [blk4_mul, a.mul_inv, b.mul_inv, blk4_one]
  inv_val := by rw [blk4_mul, a.inv_mul, b.inv_mul, blk4_one]

theorem coe_diagGL (a b : GL (Fin 2) F) :
    ((diagGL a b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blk4 (a : Matrix (Fin 2) (Fin 2) F) (b : Matrix (Fin 2) (Fin 2) F) := rfl

theorem diagGL_mul (a b a' b' : GL (Fin 2) F) :
    diagGL a b * diagGL a' b' = diagGL (a * a') (b * b') := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagGL, blk4_mul]

theorem diagGL_one : (diagGL (1 : GL (Fin 2) F) 1) = 1 := by
  apply Units.ext
  simp only [coe_diagGL, Units.val_one, blk4_one]

theorem diagGL_inv (a b : GL (Fin 2) F) : (diagGL a b)⁻¹ = diagGL a⁻¹ b⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [diagGL_mul, mul_inv_cancel, mul_inv_cancel, diagGL_one])

theorem det_diagGL (a b : GL (Fin 2) F) :
    ((diagGL a b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det :=
  det_blk4 _ _

theorem diagGL_inj {a b a' b' : GL (Fin 2) F} (h : diagGL a b = diagGL a' b') :
    a = a' ∧ b = b' := by
  have := blk4_inj (congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h)
  exact ⟨Units.ext this.1, Units.ext this.2⟩

variable (F) in
@[expose] def diagGLHom : GL (Fin 2) F × GL (Fin 2) F →* GL (Fin 4) F where
  toFun p := diagGL p.1 p.2
  map_one' := diagGL_one
  map_mul' p q := (diagGL_mul p.1 p.2 q.1 q.2).symm

variable (F) in
@[expose] def blkL : GL (Fin 2) F →* GL (Fin 4) F :=
  (diagGLHom F).comp (MonoidHom.inl _ _)

variable (F) in
@[expose] def blkR : GL (Fin 2) F →* GL (Fin 4) F :=
  (diagGLHom F).comp (MonoidHom.inr _ _)

theorem blkL_apply (a : GL (Fin 2) F) : blkL F a = diagGL a 1 := rfl

theorem blkR_apply (a : GL (Fin 2) F) : blkR F a = diagGL 1 a := rfl

theorem blkL_injective : Function.Injective (blkL F) := fun _ _ h => (diagGL_inj h).1

theorem blkR_injective : Function.Injective (blkR F) := fun _ _ h => (diagGL_inj h).2

theorem diagGL_eq_blkL_mul_blkR (a b : GL (Fin 2) F) : diagGL a b = blkL F a * blkR F b := by
  rw [blkL_apply, blkR_apply, diagGL_mul, mul_one, one_mul]

theorem blkL_mul_blkR_comm (a b : GL (Fin 2) F) : blkL F a * blkR F b = blkR F b * blkL F a := by
  rw [blkL_apply, blkR_apply, diagGL_mul, diagGL_mul, mul_one, one_mul, mul_one, one_mul]

variable (F) in
@[expose] def swapGL : GL (Fin 4) F :=
  ⟨wMat, wMat, wMat_mul_self, wMat_mul_self⟩

theorem coe_swapGL : ((swapGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = wMat := rfl

theorem swapGL_mul_self : swapGL F * swapGL F = 1 := Units.ext wMat_mul_self

theorem swapGL_inv : (swapGL F)⁻¹ = swapGL F :=
  inv_eq_of_mul_eq_one_right swapGL_mul_self

theorem swapGL_mul_diagGL_mul_inv (a b : GL (Fin 2) F) :
    swapGL F * diagGL a b * (swapGL F)⁻¹ = diagGL b a := by
  rw [swapGL_inv]
  apply Units.ext
  simp only [Units.val_mul, coe_swapGL, coe_diagGL]
  exact wMat_mul_blk4_mul_wMat _ _

variable (F) in
@[expose] def yGL : GL (Fin 4) F := diagGL (-1) 1

variable (F) in
@[expose] def xyGL : GL (Fin 4) F := diagGL 1 (-1)

variable (F) in
@[expose] def xGL : GL (Fin 4) F := diagGL (-1) (-1)

theorem yGL_mul_self : yGL F * yGL F = 1 := by
  rw [yGL, diagGL_mul, mul_one, neg_mul_neg, one_mul, diagGL_one]

theorem xyGL_mul_self : xyGL F * xyGL F = 1 := by
  rw [xyGL, diagGL_mul, mul_one, neg_mul_neg, one_mul, diagGL_one]

theorem xGL_mul_self : xGL F * xGL F = 1 := by
  rw [xGL, diagGL_mul, neg_mul_neg, one_mul, diagGL_one]

theorem xGL_eq_yGL_mul_xyGL : xGL F = yGL F * xyGL F := by
  rw [xGL, yGL, xyGL, diagGL_mul, mul_one, one_mul]

theorem yGL_mul_xyGL_comm : yGL F * xyGL F = xyGL F * yGL F := by
  rw [yGL, xyGL, diagGL_mul, diagGL_mul, mul_one, one_mul]

theorem xGL_eq_neg_one : xGL F = -1 := by
  apply Units.ext
  rw [xGL, coe_diagGL, Units.val_neg, Units.val_one]
  simp only [Units.val_neg, Units.val_one, blk4_neg, blk4_one]

theorem swapGL_mul_yGL_mul_inv : swapGL F * yGL F * (swapGL F)⁻¹ = xyGL F := by
  rw [yGL, xyGL, swapGL_mul_diagGL_mul_inv]

theorem swapGL_mul_xyGL_mul_inv : swapGL F * xyGL F * (swapGL F)⁻¹ = yGL F := by
  rw [yGL, xyGL, swapGL_mul_diagGL_mul_inv]

theorem xGL_comm (g : GL (Fin 4) F) : xGL F * g = g * xGL F := by
  rw [xGL_eq_neg_one]
  apply Units.ext
  simp

end DiagGL

section Centralizer

variable {F : Type} [Field F]

theorem det_wMat : (wMat : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have hR : (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1) *
        fromBlocks (-1) 0 0 1 := by
    simp only [fromBlocks_multiply]
    simp
  rw [wMat, Matrix.det_reindexAlgEquiv, hR, det_mul, det_mul, det_mul]
  simp only [det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]
  simp [Matrix.det_neg]

theorem exists_blk4_of_comm (h2 : (2 : F) ≠ 0) {g : Matrix (Fin 4) (Fin 4) F}
    (h : g * blk4 (-1) 1 = blk4 (-1) 1 * g) :
    ∃ A B : Matrix (Fin 2) (Fin 2) F, g = blk4 A B := by
  obtain ⟨g', rfl⟩ := (Matrix.reindexAlgEquiv F F e4).surjective g
  rw [blk4_eq_reindex, ← map_mul, ← map_mul] at h
  have h' := (Matrix.reindexAlgEquiv F F e4).injective h
  rw [← fromBlocks_toBlocks g', fromBlocks_multiply, fromBlocks_multiply] at h'
  simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.neg_mul,
    Matrix.one_mul, Matrix.zero_mul, zero_add] at h'
  obtain ⟨-, hB, hC, -⟩ := fromBlocks_inj.1 h'
  have key : ∀ M : Matrix (Fin 2) (Fin 2) F, M = -M → M = 0 := fun M hM => by
    have h3 : (2 : F) • M = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hM]
      exact neg_add_cancel M
    exact (smul_eq_zero.mp h3).resolve_left h2
  have hB0 := key _ hB
  have hC0 : g'.toBlocks₂₁ = 0 := key _ hC.symm
  refine ⟨g'.toBlocks₁₁, g'.toBlocks₂₂, ?_⟩
  rw [blk4_eq_reindex]
  congr 1
  conv_lhs => rw [← fromBlocks_toBlocks g']
  rw [hB0, hC0]

end Centralizer

section Model

variable {F : Type} [Field F]

variable (F) in
@[expose] def detOne (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) F).det = 1}
  mul_mem' {a b} ha hb := by
    change ((a * b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1
    rw [Units.val_mul, det_mul, show (a : Matrix (Fin n) (Fin n) F).det = 1 from ha,
      show (b : Matrix (Fin n) (Fin n) F).det = 1 from hb, one_mul]
  one_mem' := by
    change ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1
    simp
  inv_mem' {a} ha := by
    have h := congrArg Matrix.det a.mul_inv
    rw [det_mul, det_one, show (a : Matrix (Fin n) (Fin n) F).det = 1 from ha, one_mul] at h
    exact h

theorem mem_detOne {n : ℕ} {g : GL (Fin n) F} :
    g ∈ detOne F n ↔ (g : Matrix (Fin n) (Fin n) F).det = 1 := Iff.rfl

theorem statedSL_eq_detOne (n : ℕ) : StatedSL n F = detOne F n :=
  Subgroup.closure_eq (detOne F n)

variable (F) in
structure ModelData where
  U2 : Subgroup (GL (Fin 2) F)
  U4 : Subgroup (GL (Fin 4) F)
  K4 : Subgroup (GL (Fin 4) F)
  H2 : Subgroup (GL (Fin 2) F)
  mem_K4 : ∀ g : GL (Fin 4) F, g ∈ K4 ↔ g ∈ U4 ∧ (g : Matrix (Fin 4) (Fin 4) F).det = 1
  mem_H2 : ∀ a : GL (Fin 2) F, a ∈ H2 ↔ a ∈ U2 ∧ (a : Matrix (Fin 2) (Fin 2) F).det = 1
  diag_mem_iff : ∀ a b : GL (Fin 2) F, diagGL a b ∈ U4 ↔ a ∈ U2 ∧ b ∈ U2
  neg_mem : (-1 : GL (Fin 2) F) ∈ U2
  swap_mem : swapGL F ∈ U4

namespace ModelData

variable (M : ModelData F)

theorem diagGL_mem_K4_iff {a b : GL (Fin 2) F} :
    diagGL a b ∈ M.K4 ↔ a ∈ M.U2 ∧ b ∈ M.U2 ∧
      (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [M.mem_K4, M.diag_mem_iff, det_diagGL]
  tauto

theorem yGL_mem_K4 : yGL F ∈ M.K4 := by
  rw [yGL, diagGL_mem_K4_iff]
  refine ⟨M.neg_mem, M.U2.one_mem, ?_⟩
  simp [Matrix.det_neg]

theorem xyGL_mem_K4 : xyGL F ∈ M.K4 := by
  rw [xyGL, diagGL_mem_K4_iff]
  refine ⟨M.U2.one_mem, M.neg_mem, ?_⟩
  simp [Matrix.det_neg]

theorem xGL_mem_K4 : xGL F ∈ M.K4 := by
  rw [xGL, diagGL_mem_K4_iff]
  refine ⟨M.neg_mem, M.neg_mem, ?_⟩
  simp [Matrix.det_neg]

theorem swapGL_mem_K4 : swapGL F ∈ M.K4 :=
  (M.mem_K4 _).2 ⟨M.swap_mem, by rw [coe_swapGL]; exact det_wMat⟩

@[expose] def xK : ↥M.K4 := ⟨xGL F, M.xGL_mem_K4⟩

@[expose] def yK : ↥M.K4 := ⟨yGL F, M.yGL_mem_K4⟩

@[expose] def xyK : ↥M.K4 := ⟨xyGL F, M.xyGL_mem_K4⟩

@[expose] def wK : ↥M.K4 := ⟨swapGL F, M.swapGL_mem_K4⟩

theorem neg_one_mem_H2 : (-1 : GL (Fin 2) F) ∈ M.H2 :=
  (M.mem_H2 _).2 ⟨M.neg_mem, by simp [Matrix.det_neg]⟩

theorem blkL_mem_K4 {a : GL (Fin 2) F} (ha : a ∈ M.H2) : blkL F a ∈ M.K4 := by
  rw [blkL_apply, diagGL_mem_K4_iff]
  obtain ⟨h1, h2⟩ := (M.mem_H2 a).1 ha
  exact ⟨h1, M.U2.one_mem, by rw [h2]; simp⟩

theorem blkR_mem_K4 {a : GL (Fin 2) F} (ha : a ∈ M.H2) : blkR F a ∈ M.K4 := by
  rw [blkR_apply, diagGL_mem_K4_iff]
  obtain ⟨h1, h2⟩ := (M.mem_H2 a).1 ha
  exact ⟨M.U2.one_mem, h1, by rw [h2]; simp⟩

theorem yGL_eq_blkL : yGL F = blkL F (-1) := rfl

theorem xyGL_eq_blkR : xyGL F = blkR F (-1) := rfl

theorem exists_diagGL_of_comm (h2 : (2 : F) ≠ 0) {g : GL (Fin 4) F} (hg : g ∈ M.K4)
    (hc : g * yGL F = yGL F * g) :
    ∃ a b : GL (Fin 2) F, g = diagGL a b ∧ a ∈ M.U2 ∧ b ∈ M.U2 ∧
      (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have hy : ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 (-1) 1 := by
    rw [yGL, coe_diagGL]
    simp
  have hc' : g⁻¹ * yGL F = yGL F * g⁻¹ :=
    (Commute.inv_left (show Commute g (yGL F) from hc)).eq
  obtain ⟨A, B, hAB⟩ := exists_blk4_of_comm h2 (g := (g : Matrix (Fin 4) (Fin 4) F))
    (by
      have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) hc
      simpa only [Units.val_mul, hy] using this)
  obtain ⟨A', B', hAB'⟩ := exists_blk4_of_comm h2
    (g := ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (by
      have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) hc'
      simpa only [Units.val_mul, hy] using this)
  have h1 : blk4 (A * A') (B * B') = blk4 1 1 := by
    rw [← blk4_mul, ← hAB, ← hAB', g.mul_inv, blk4_one]
  have h2' : blk4 (A' * A) (B' * B) = blk4 1 1 := by
    rw [← blk4_mul, ← hAB, ← hAB', g.inv_mul, blk4_one]
  obtain ⟨hA1, hB1⟩ := blk4_inj h1
  obtain ⟨hA2, hB2⟩ := blk4_inj h2'
  refine ⟨⟨A, A', hA1, hA2⟩, ⟨B, B', hB1, hB2⟩, ?_, ?_⟩
  · apply Units.ext
    rw [coe_diagGL]
    exact hAB
  · have hmem : diagGL ⟨A, A', hA1, hA2⟩ ⟨B, B', hB1, hB2⟩ ∈ M.K4 := by
      have : g = diagGL ⟨A, A', hA1, hA2⟩ ⟨B, B', hB1, hB2⟩ := by
        apply Units.ext
        rw [coe_diagGL]
        exact hAB
      rw [← this]
      exact hg
    exact (diagGL_mem_K4_iff M).1 hmem

end ModelData

end Model

section Linear

variable (F : Type) [Field F]

@[expose] def ModelData.lin : ModelData F where
  U2 := ⊤
  U4 := ⊤
  K4 := StatedSL 4 F
  H2 := StatedSL 2 F
  mem_K4 g := by rw [statedSL_eq_detOne]; simp [mem_detOne]
  mem_H2 g := by rw [statedSL_eq_detOne]; simp [mem_detOne]
  diag_mem_iff _ _ := by simp
  neg_mem := Subgroup.mem_top _
  swap_mem := Subgroup.mem_top _

end Linear

section Unitary

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] def uniGL (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {A | conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) = 1}
  mul_mem' {A B} hA hB := by
    have hA' : conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) = 1 := hA
    have hB' : conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1 := hB
    change conjTr σ ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    have e : conjTr σ ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
        ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) =
        conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    rw [Units.val_mul, e, hA', Matrix.mul_one, hB']
  one_mem' := by
    change conjTr σ ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    simp [conjTr_one]
  inv_mem' {A} hA := by
    have hA' : conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) = 1 := hA
    have hAB : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    change conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    have key : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) *
        (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix _ _ F)) *
          ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) =
        conjTr σ ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) *
          ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    rw [hA', Matrix.mul_one, hAB, conjTr_one, Matrix.one_mul] at key
    exact key

theorem mem_uniGL {n : ℕ} {A : GL (Fin n) F} :
    A ∈ uniGL σ n ↔
      conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) = 1 := Iff.rfl

theorem conjTr_blk4 (X Y : Matrix (Fin 2) (Fin 2) F) :
    conjTr σ (blk4 X Y) = blk4 (conjTr σ X) (conjTr σ Y) :=
  hstar_diagBlock (σ := (σ : F →+* F)) X Y

theorem conjTr_neg_one {n : ℕ} : conjTr σ (-1 : Matrix (Fin n) (Fin n) F) = -1 := by
  ext i j
  simp [conjTr, Matrix.one_apply, eq_comm]

theorem conjTr_wMat : conjTr σ (wMat : Matrix (Fin 4) (Fin 4) F) = wMat := by
  have h : conjTr σ (wMat : Matrix (Fin 4) (Fin 4) F) =
      Matrix.reindexAlgEquiv F F e4
        (((fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ)ᵀ) := by
    ext a b
    simp [conjTr, wMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  rw [h, wMat]
  congr 1
  simp [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem SUid_four_eq_inf : SUid σ 4 = uniGL σ 4 ⊓ detOne F 4 := by
  ext g
  simp only [mem_SUid, Subgroup.mem_inf, mem_uniGL, mem_detOne]
  exact and_comm

theorem SUid_two_eq_inf : SUid σ 2 = uniGL σ 2 ⊓ detOne F 2 := by
  ext g
  simp only [mem_SUid, Subgroup.mem_inf, mem_uniGL, mem_detOne]
  exact and_comm

@[expose] noncomputable def ModelData.uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) : ModelData F where
  U2 := uniGL (unitaryInvolution F p f) 2
  U4 := uniGL (unitaryInvolution F p f) 4
  K4 := StatedSU 4 (p ^ f) F
  H2 := StatedSU 2 (p ^ f) F
  mem_K4 g := by
    rw [← SUid_eq_statedSU hF, SUid_four_eq_inf]
    simp [mem_detOne]
  mem_H2 g := by
    rw [← SUid_eq_statedSU hF, SUid_two_eq_inf]
    simp [mem_detOne]
  diag_mem_iff a b := by
    rw [mem_uniGL, mem_uniGL, mem_uniGL, coe_diagGL, conjTr_blk4, blk4_mul, ← blk4_one]
    constructor
    · intro h
      exact blk4_inj h
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
  neg_mem := by
    rw [mem_uniGL]
    simp only [Units.val_neg, Units.val_one]
    rw [conjTr_neg_one]
    simp
  swap_mem := by
    rw [mem_uniGL, coe_swapGL, conjTr_wMat]
    exact wMat_mul_self

end Unitary

section Identification

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

theorem exists_prime_pow_of_card_eq_sq {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) : ∃ (p f : ℕ) (_ : Fact p.Prime) (_ : CharP F p), q = p ^ f := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card (K := F) p
  have hq : q ∣ p ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hF]
    exact Dvd.intro q (sq q).symm
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpp).1 hq
  exact ⟨p, f, ⟨hpp⟩, hp, hf⟩

theorem two_ne_zero_of_odd_card {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 :=
    CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact_mod_cast h2)
  have h0 := FiniteField.even_card_iff_char_two.1 hchar
  rw [← Nat.card_eq_fintype_card] at h0
  have h1 : Even (Nat.card F) := Nat.even_iff.2 h0
  exact (Nat.not_even_iff_odd.2 h) h1

theorem prime_ne_two_of_odd_card {F : Type} [Field F] [Finite F] {p : ℕ} [CharP F p]
    (h : Odd (Nat.card F)) : p ≠ 2 := by
  rintro rfl
  have h2 : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  exact two_ne_zero_of_odd_card h (by exact_mod_cast h2)

theorem nonempty_sl2_equiv_uni_H2 {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f) ≃*
      ↥(ModelData.uni hF).H2) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  exact ⟨((hypEquiv hζ0 hζ).trans (conjEquiv P hP)).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hF 2))⟩

noncomputable def lin_sl2_equiv_H2 (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(ModelData.lin F).H2 :=
  CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F

end Identification

end CFSG.GH74.L5U5
