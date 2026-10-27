module

public import CFSG.LieType.SpecialLinear.Block222.Basic
public import CFSG.LieType.SpecialLinear.CurtisDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

@[expose] def upFormMat (B : Matrix (Fin 2) (Fin c ⊕ Fin 2) F) (E : Matrix (Fin c) (Fin 2) F) :
    Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F :=
  Matrix.fromBlocks 1 B 0 (Matrix.fromBlocks 1 E 0 1)

@[expose] def lowFormMat (C : Matrix (Fin c ⊕ Fin 2) (Fin 2) F) (E : Matrix (Fin 2) (Fin c) F) :
    Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F :=
  Matrix.fromBlocks 1 0 C (Matrix.fromBlocks 1 0 E 1)

theorem det_upFormMat (B E) : (upFormMat c F B E).det = 1 := by
  rw [upFormMat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_lowFormMat (C E) : (lowFormMat c F C E).det = 1 := by
  rw [lowFormMat, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂]
  simp

@[expose] def upFormSL (B : Matrix (Fin 2) (Fin c ⊕ Fin 2) F) (E : Matrix (Fin c) (Fin 2) F) :
    SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F :=
  ⟨upFormMat c F B E, det_upFormMat c F B E⟩

@[expose] def lowFormSL (C : Matrix (Fin c ⊕ Fin 2) (Fin 2) F) (E : Matrix (Fin 2) (Fin c) F) :
    SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F :=
  ⟨lowFormMat c F C E, det_lowFormMat c F C E⟩

theorem coe_upFormSL (B E) : ((upFormSL c F B E : SpecialLinearGroup
    (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2))
      (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) = upFormMat c F B E := rfl

theorem coe_lowFormSL (C E) : ((lowFormSL c F C E : SpecialLinearGroup
    (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2))
      (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) = lowFormMat c F C E := rfl

theorem upFormSL_diag (B E) (i : Fin 2 ⊕ (Fin c ⊕ Fin 2)) :
    ((upFormSL c F B E : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
      Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) i i = 1 := by
  rcases i with a | (s | k) <;> simp [upFormSL, upFormMat]

theorem upFormSL_off (B E) {i j : Fin 2 ⊕ (Fin c ⊕ Fin 2)}
    (hle : blkSum222 c i ≥ blkSum222 c j) (hij : i ≠ j) :
    ((upFormSL c F B E : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
      Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) i j = 0 := by
  rcases i with a | (s | k) <;> rcases j with b | (t | l) <;>
    simp only [upFormSL, upFormMat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, blkSum222] at hle ⊢
  · rw [Matrix.one_apply_ne (by simpa using hij)]
  · omega
  · omega
  · simp
  · rw [Matrix.one_apply_ne (by simpa using hij)]
  · omega
  · simp
  · simp
  · rw [Matrix.one_apply_ne (by simpa using hij)]

theorem lowFormSL_diag (C E) (i : Fin 2 ⊕ (Fin c ⊕ Fin 2)) :
    ((lowFormSL c F C E : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
      Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) i i = 1 := by
  rcases i with a | (s | k) <;> simp [lowFormSL, lowFormMat]

theorem lowFormSL_off (C E) {i j : Fin 2 ⊕ (Fin c ⊕ Fin 2)}
    (hle : blkSum222 c i ≤ blkSum222 c j) (hij : i ≠ j) :
    ((lowFormSL c F C E : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
      Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) i j = 0 := by
  rcases i with a | (s | k) <;> rcases j with b | (t | l) <;>
    simp only [lowFormSL, lowFormMat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, blkSum222] at hle ⊢
  · rw [Matrix.one_apply_ne (by simpa using hij)]
  · simp
  · simp
  · omega
  · rw [Matrix.one_apply_ne (by simpa using hij)]
  · simp
  · omega
  · omega
  · rw [Matrix.one_apply_ne (by simpa using hij)]

@[expose] def blockRadicalSum222 : Subgroup (SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :=
  Subgroup.closure {q | ∃ (B : Matrix (Fin 2) (Fin c ⊕ Fin 2) F) (E : Matrix (Fin c) (Fin 2) F),
    q = upFormSL c F B E}

@[expose] def blockRadicalLowerSum222 :
    Subgroup (SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :=
  Subgroup.closure {q | ∃ (C : Matrix (Fin c ⊕ Fin 2) (Fin 2) F) (E : Matrix (Fin 2) (Fin c) F),
    q = lowFormSL c F C E}

theorem upFormSL_mem (B E) : upFormSL c F B E ∈ blockRadicalSum222 c F :=
  Subgroup.subset_closure ⟨B, E, rfl⟩

theorem lowFormSL_mem (C E) : lowFormSL c F C E ∈ blockRadicalLowerSum222 c F :=
  Subgroup.subset_closure ⟨C, E, rfl⟩

theorem coe_triDiagHom (g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
    SpecialLinearGroup (Fin 2) F) :
    ((triDiagHom c F g : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
        Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) =
      triDiagMat c F (g.1 : Matrix (Fin 2) (Fin 2) F) (g.2.1 : Matrix (Fin c) (Fin c) F)
        (g.2.2 : Matrix (Fin 2) (Fin 2) F) := rfl

theorem triDiagHom_conj_upForm_mem (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F)
    (B : Matrix (Fin 2) (Fin c ⊕ Fin 2) F) (E : Matrix (Fin c) (Fin 2) F) :
    triDiagHom c F g * upFormSL c F B E * (triDiagHom c F g)⁻¹ ∈ blockRadicalSum222 c F := by
  set A : Matrix (Fin 2) (Fin 2) F := (g.1 : Matrix (Fin 2) (Fin 2) F)
  set D : Matrix (Fin c) (Fin c) F := (g.2.1 : Matrix (Fin c) (Fin c) F)
  set G : Matrix (Fin 2) (Fin 2) F := (g.2.2 : Matrix (Fin 2) (Fin 2) F)
  have hA : A * A⁻¹ = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel g.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_inv] at h
    rw [Matrix.inv_eq_right_inv h]
    exact h
  have hD : D * D⁻¹ = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin c) F =>
      (x : Matrix (Fin c) (Fin c) F)) (mul_inv_cancel g.2.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_inv] at h
    rw [Matrix.inv_eq_right_inv h]
    exact h
  have hG : G * G⁻¹ = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel g.2.2)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_inv] at h
    rw [Matrix.inv_eq_right_inv h]
    exact h
  have hAadj : A * A.adjugate = 1 := by
    rw [Matrix.mul_adjugate, show A.det = 1 from g.1.2, one_smul]
  have hDadj : D * D.adjugate = 1 := by
    rw [Matrix.mul_adjugate, show D.det = 1 from g.2.1.2, one_smul]
  have hGadj : G * G.adjugate = 1 := by
    rw [Matrix.mul_adjugate, show G.det = 1 from g.2.2.2, one_smul]
  have hAinv : (((g⁻¹).1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A⁻¹ := by
    show ((g.1⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A⁻¹
    rw [Matrix.SpecialLinearGroup.coe_inv]
    exact (Matrix.inv_eq_right_inv hAadj).symm
  have hDinv : (((g⁻¹).2.1 : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F) = D⁻¹ := by
    show ((g.2.1⁻¹ : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F) = D⁻¹
    rw [Matrix.SpecialLinearGroup.coe_inv]
    exact (Matrix.inv_eq_right_inv hDadj).symm
  have hGinv : (((g⁻¹).2.2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = G⁻¹ := by
    show ((g.2.2⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = G⁻¹
    rw [Matrix.SpecialLinearGroup.coe_inv]
    exact (Matrix.inv_eq_right_inv hGadj).symm
  have hconj : triDiagHom c F g * upFormSL c F B E * (triDiagHom c F g)⁻¹ =
      upFormSL c F (A * B * Matrix.fromBlocks D⁻¹ 0 0 G⁻¹) (D * E * G⁻¹) := by
    rw [← map_inv]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_triDiagHom, coe_upFormSL,
      triDiagMat, upFormMat, hAinv, hDinv, hGinv]
    simp only [show ((g.1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A from rfl,
      show ((g.2.1 : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F) = D from rfl,
      show ((g.2.2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = G from rfl,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, hA, hD, hG, Matrix.mul_one]
  rw [hconj]
  exact upFormSL_mem c F _ _

theorem triDiagHom_conj_lowForm_mem (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F)
    (C : Matrix (Fin c ⊕ Fin 2) (Fin 2) F) (E : Matrix (Fin 2) (Fin c) F) :
    triDiagHom c F g * lowFormSL c F C E * (triDiagHom c F g)⁻¹ ∈ blockRadicalLowerSum222 c F := by
  set A : Matrix (Fin 2) (Fin 2) F := (g.1 : Matrix (Fin 2) (Fin 2) F)
  set D : Matrix (Fin c) (Fin c) F := (g.2.1 : Matrix (Fin c) (Fin c) F)
  set G : Matrix (Fin 2) (Fin 2) F := (g.2.2 : Matrix (Fin 2) (Fin 2) F)
  have hA : A * A⁻¹ = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel g.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_inv] at h
    rw [Matrix.inv_eq_right_inv h]
    exact h
  have hD : D * D⁻¹ = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin c) F =>
      (x : Matrix (Fin c) (Fin c) F)) (mul_inv_cancel g.2.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_inv] at h
    rw [Matrix.inv_eq_right_inv h]
    exact h
  have hG : G * G⁻¹ = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel g.2.2)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_inv] at h
    rw [Matrix.inv_eq_right_inv h]
    exact h
  have hAadj : A * A.adjugate = 1 := by
    rw [Matrix.mul_adjugate, show A.det = 1 from g.1.2, one_smul]
  have hDadj : D * D.adjugate = 1 := by
    rw [Matrix.mul_adjugate, show D.det = 1 from g.2.1.2, one_smul]
  have hGadj : G * G.adjugate = 1 := by
    rw [Matrix.mul_adjugate, show G.det = 1 from g.2.2.2, one_smul]
  have hAinv : (((g⁻¹).1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A⁻¹ := by
    show ((g.1⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A⁻¹
    rw [Matrix.SpecialLinearGroup.coe_inv]
    exact (Matrix.inv_eq_right_inv hAadj).symm
  have hDinv : (((g⁻¹).2.1 : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F) = D⁻¹ := by
    show ((g.2.1⁻¹ : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F) = D⁻¹
    rw [Matrix.SpecialLinearGroup.coe_inv]
    exact (Matrix.inv_eq_right_inv hDadj).symm
  have hGinv : (((g⁻¹).2.2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = G⁻¹ := by
    show ((g.2.2⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = G⁻¹
    rw [Matrix.SpecialLinearGroup.coe_inv]
    exact (Matrix.inv_eq_right_inv hGadj).symm
  have hconj : triDiagHom c F g * lowFormSL c F C E * (triDiagHom c F g)⁻¹ =
      lowFormSL c F (Matrix.fromBlocks D 0 0 G * C * A⁻¹) ((G * E) * D⁻¹) := by
    rw [← map_inv]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_triDiagHom, coe_lowFormSL,
      triDiagMat, lowFormMat, hAinv, hDinv, hGinv]
    simp only [show ((g.1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A from rfl,
      show ((g.2.1 : SpecialLinearGroup (Fin c) F) : Matrix (Fin c) (Fin c) F) = D from rfl,
      show ((g.2.2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = G from rfl,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, hA, hD, hG, Matrix.mul_one]
  rw [hconj]
  exact lowFormSL_mem c F _ _

theorem blockRadicalSum222_normalized (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F)
    {q : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F}
    (hq : q ∈ blockRadicalSum222 c F) :
    triDiagHom c F g * q * (triDiagHom c F g)⁻¹ ∈ blockRadicalSum222 c F := by
  let φ : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F →*
      SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F :=
    { toFun := fun x => triDiagHom c F g * x * (triDiagHom c F g)⁻¹
      map_one' := by group
      map_mul' := by intro x y; group }
  have hle : blockRadicalSum222 c F ≤ (blockRadicalSum222 c F).comap φ := by
    rw [blockRadicalSum222]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨B, E, rfl⟩
    exact triDiagHom_conj_upForm_mem c F g B E
  exact hle hq

theorem blockRadicalLowerSum222_normalized (g : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F)
    {q : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F}
    (hq : q ∈ blockRadicalLowerSum222 c F) :
    triDiagHom c F g * q * (triDiagHom c F g)⁻¹ ∈ blockRadicalLowerSum222 c F := by
  let φ : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F →*
      SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F :=
    { toFun := fun x => triDiagHom c F g * x * (triDiagHom c F g)⁻¹
      map_one' := by group
      map_mul' := by intro x y; group }
  have hle : blockRadicalLowerSum222 c F ≤ (blockRadicalLowerSum222 c F).comap φ := by
    rw [blockRadicalLowerSum222]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨C, E, rfl⟩
    exact triDiagHom_conj_lowForm_mem c F g C E
  exact hle hq

@[expose] def blockRadical222 : Subgroup (SpecialLinearGroup (Fin (c + 4)) F) :=
  (blockRadicalSum222 c F).map (reindexSL c F).toMonoidHom

@[expose] def blockRadicalLower222 : Subgroup (SpecialLinearGroup (Fin (c + 4)) F) :=
  (blockRadicalLowerSum222 c F).map (reindexSL c F).toMonoidHom

theorem mem_blockRadical222_reindexSL_iff (x : SpecialLinearGroup
    (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    reindexSL c F x ∈ blockRadical222 c F ↔ x ∈ blockRadicalSum222 c F :=
  Subgroup.mem_map_iff_mem (reindexSL c F).injective

theorem mem_blockRadicalLower222_reindexSL_iff (x : SpecialLinearGroup
    (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F) :
    reindexSL c F x ∈ blockRadicalLower222 c F ↔ x ∈ blockRadicalLowerSum222 c F :=
  Subgroup.mem_map_iff_mem (reindexSL c F).injective

theorem blockRadical222_normalized {m x : SpecialLinearGroup (Fin (c + 4)) F}
    (hm : m ∈ (blockEmbed222 c F).range) (hx : x ∈ blockRadical222 c F) :
    m * x * m⁻¹ ∈ blockRadical222 c F := by
  obtain ⟨g, rfl⟩ := hm
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
  have hb : blockEmbed222 c F g = reindexSL c F (triDiagHom c F g) := rfl
  rw [hb]
  change reindexSL c F (triDiagHom c F g) * reindexSL c F q *
      (reindexSL c F (triDiagHom c F g))⁻¹ ∈ blockRadical222 c F
  rw [← map_mul, ← map_inv, ← map_mul, mem_blockRadical222_reindexSL_iff]
  exact blockRadicalSum222_normalized c F g hq

theorem blockRadicalLower222_normalized {m x : SpecialLinearGroup (Fin (c + 4)) F}
    (hm : m ∈ (blockEmbed222 c F).range) (hx : x ∈ blockRadicalLower222 c F) :
    m * x * m⁻¹ ∈ blockRadicalLower222 c F := by
  obtain ⟨g, rfl⟩ := hm
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
  have hb : blockEmbed222 c F g = reindexSL c F (triDiagHom c F g) := rfl
  rw [hb]
  change reindexSL c F (triDiagHom c F g) * reindexSL c F q *
      (reindexSL c F (triDiagHom c F g))⁻¹ ∈ blockRadicalLower222 c F
  rw [← map_mul, ← map_inv, ← map_mul, mem_blockRadicalLower222_reindexSL_iff]
  exact blockRadicalLowerSum222_normalized c F g hq

theorem reindexSL_upFormSL_mem (B E) :
    reindexSL c F (upFormSL c F B E) ∈ blockRadical222 c F :=
  (mem_blockRadical222_reindexSL_iff c F _).mpr (upFormSL_mem c F B E)

theorem reindexSL_lowFormSL_mem (C E) :
    reindexSL c F (lowFormSL c F C E) ∈ blockRadicalLower222 c F :=
  (mem_blockRadicalLower222_reindexSL_iff c F _).mpr (lowFormSL_mem c F C E)

theorem reindexSL_apply (x : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F)
    (i j : Fin (c + 4)) :
    ((reindexSL c F x : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) i j =
      (x : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F)
        ((e222 c).symm i) ((e222 c).symm j) := by
  rw [coe_reindexSL, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]

theorem blockRadical222_le_U [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    blockRadical222 c F ≤ (curtisDatum (c + 3) F p).U := by
  rw [blockRadical222, Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).mpr ?_
  rintro q ⟨B, E, rfl⟩
  change reindexSL c F (upFormSL c F B E) ∈ (curtisDatum (c + 3) F p).U
  rw [mem_curtisDatum_U_iff]
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [reindexSL_apply]
    exact upFormSL_diag c F B E _
  · rw [reindexSL_apply]
    refine upFormSL_off c F B E ?_ ?_
    · rw [← blk222_e222, ← blk222_e222, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact blk222_le_of_le (c := c) (le_of_lt hji)
    · exact fun h => absurd ((e222 c).symm.injective h) (ne_of_gt hji)

theorem blockRadicalLower222_le_L [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    blockRadicalLower222 c F ≤ (curtisDatum (c + 3) F p).L := by
  rw [blockRadicalLower222, Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).mpr ?_
  rintro q ⟨C, E, rfl⟩
  change reindexSL c F (lowFormSL c F C E) ∈ (curtisDatum (c + 3) F p).L
  rw [mem_curtisDatum_L_iff]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [reindexSL_apply]
    exact lowFormSL_diag c F C E _
  · rw [reindexSL_apply]
    refine lowFormSL_off c F C E ?_ ?_
    · rw [← blk222_e222, ← blk222_e222, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact blk222_le_of_le (c := c) (le_of_lt hij)
    · exact fun h => absurd ((e222 c).symm.injective h) (ne_of_lt hij)

end

end CFSG.LieType.SpecialLinear
