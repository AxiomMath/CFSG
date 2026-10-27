module

public import CFSG.LinearAlgebra.UnipotentRadical
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddSL3
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

open Matrix
open CFSG.RankThree.SubgroupLists
open CFSG.RankThree.PartTwo.Sec4.L34Odd (embSL embSL_coe)
open scoped MatrixGroups

namespace CFSG.LinearAlgebra.SLThreeLevi

variable {K : Type*} [Field K]

@[expose] def blockMat (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, b 0;
     A 1 0, A 1 1, b 1;
     c 0, c 1, d]

@[expose] def blockb (M : Matrix (Fin 3) (Fin 3) K) : Fin 2 → K :=
  fun i => M i.castSucc 2

@[expose] def blockc (M : Matrix (Fin 3) (Fin 3) K) : Fin 2 → K :=
  fun j => M 2 j.castSucc

@[expose] def blockd (M : Matrix (Fin 3) (Fin 3) K) : K := M 2 2

@[simp] theorem blockb_apply (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 2) :
    blockb M i = M i.castSucc 2 := rfl
@[simp] theorem blockc_apply (M : Matrix (Fin 3) (Fin 3) K) (j : Fin 2) :
    blockc M j = M 2 j.castSucc := rfl
@[simp] theorem blockd_apply (M : Matrix (Fin 3) (Fin 3) K) : blockd M = M 2 2 := rfl

theorem blockMat_ulBlock_blockb_blockc_blockd (M : Matrix (Fin 3) (Fin 3) K) :
    blockMat (ulBlock M) (blockb M) (blockc M) (blockd M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, ulBlock, blockb, blockc, blockd]

@[expose] def e3 : Fin 3 → K := ![0, 0, 1]

@[simp] theorem e3_eq_single : e3 = Pi.single 2 (1 : K) := by
  funext i
  fin_cases i <;> simp [e3]

@[expose] def emb2 (v : Fin 2 → K) : Fin 3 → K := ![v 0, v 1, 0]

@[simp] theorem blockMat_apply_zero_zero (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 0 0 = A 0 0 := rfl
@[simp] theorem blockMat_apply_zero_one (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 0 1 = A 0 1 := rfl
@[simp] theorem blockMat_apply_zero_two (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 0 2 = b 0 := rfl
@[simp] theorem blockMat_apply_one_zero (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 1 0 = A 1 0 := rfl
@[simp] theorem blockMat_apply_one_one (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 1 1 = A 1 1 := rfl
@[simp] theorem blockMat_apply_one_two (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 1 2 = b 1 := rfl
@[simp] theorem blockMat_apply_two_zero (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 2 0 = c 0 := rfl
@[simp] theorem blockMat_apply_two_one (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 2 1 = c 1 := rfl
@[simp] theorem blockMat_apply_two_two (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d 2 2 = d := rfl

theorem blockMat_one :
    blockMat (1 : Matrix (Fin 2) (Fin 2) K) (0 : Fin 2 → K) 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem blockMat_mul (A A' : Matrix (Fin 2) (Fin 2) K) (b b' : Fin 2 → K)
    (c c' : Fin 2 → K) (d d' : K) :
    blockMat A b c d * blockMat A' b' c' d' =
      blockMat (A * A' + Matrix.vecMulVec b c')
        (fun i => (A *ᵥ b') i + b i * d')
        (fun j => (c ᵥ* A') j + d * c' j)
        (c ⬝ᵥ b' + d * d') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Matrix.vecMulVec, Matrix.vecMul, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] <;>
    ring

theorem blockMat_transpose (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    (blockMat A b c d)ᵀ = blockMat Aᵀ c b d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, Matrix.transpose_apply]

theorem blockMat_det_zero_upper (A : Matrix (Fin 2) (Fin 2) K) (c : Fin 2 → K) (d : K) :
    (blockMat A 0 c d).det = A.det * d := by
  simp [blockMat, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem blockMat_det_zero_lower (A : Matrix (Fin 2) (Fin 2) K) (b : Fin 2 → K) (d : K) :
    (blockMat A b 0 d).det = A.det * d := by
  simp [blockMat, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem blockMat_det_diag (A : Matrix (Fin 2) (Fin 2) K) (d : K) :
    (blockMat A 0 0 d).det = A.det * d :=
  blockMat_det_zero_upper A 0 d

theorem blockMat_det_upper (b : Fin 2 → K) :
    (blockMat (1 : Matrix (Fin 2) (Fin 2) K) b 0 1).det = 1 := by
  rw [blockMat_det_zero_lower]
  simp

theorem blockMat_det_lower (c : Fin 2 → K) :
    (blockMat (1 : Matrix (Fin 2) (Fin 2) K) 0 c 1).det = 1 := by
  rw [blockMat_det_zero_upper]
  simp

theorem blockMat_mulVec_emb2 (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K)
    (u : Fin 2 → K) :
    blockMat A b c d *ᵥ emb2 u = emb2 (A *ᵥ u) + (c ⬝ᵥ u) • e3 := by
  ext i
  fin_cases i <;>
    simp [blockMat, emb2, e3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockMat_mulVec_first (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K)
    (j : Fin 2) :
    blockMat A b c d *ᵥ (Pi.single j.castSucc 1) =
      emb2 (A *ᵥ (Pi.single j 1)) + c j • e3 := by
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, emb2, e3, Matrix.mulVec, dotProduct, Pi.single,
      Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockMat_mulVec_e3 (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2 → K) (d : K) :
    blockMat A b c d *ᵥ e3 = emb2 b + d • e3 := by
  ext i
  fin_cases i <;>
    simp [blockMat, emb2, e3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] theorem emb2_add (u v : Fin 2 → K) : emb2 (u + v) = emb2 u + emb2 v := by
  ext i; fin_cases i <;> simp [emb2]

@[simp] theorem emb2_smul (a : K) (u : Fin 2 → K) : emb2 (a • u) = a • emb2 u := by
  ext i; fin_cases i <;> simp [emb2]

@[simp] theorem emb2_zero : emb2 (0 : Fin 2 → K) = 0 := by
  ext i; fin_cases i <;> simp [emb2]

theorem emb2_injective : Function.Injective (emb2 : (Fin 2 → K) → Fin 3 → K) := by
  intro u v h
  funext i
  fin_cases i
  · simpa [emb2] using congrFun h 0
  · simpa [emb2] using congrFun h 1

theorem emb2_eq_zero_iff {u : Fin 2 → K} : emb2 u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext i
    fin_cases i
    · simpa [emb2] using congrFun h 0
    · simpa [emb2] using congrFun h 1
  · intro h
    rw [h]
    ext i
    fin_cases i <;> simp [emb2]

@[expose] def stdU : Submodule K (Fin 3 → K) where
  carrier := {v | v 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hx hy ⊢
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq, Pi.smul_apply] at hx ⊢
    rw [hx, smul_zero]

@[expose] def stdR : Submodule K (Fin 3 → K) where
  carrier := {v | v 0 = 0 ∧ v 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hx hy ⊢
    exact ⟨by rw [hx.1, hy.1, add_zero], by rw [hx.2, hy.2, add_zero]⟩
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq, Pi.smul_apply] at hx ⊢
    exact ⟨by rw [hx.1, smul_zero], by rw [hx.2, smul_zero]⟩

@[simp] theorem mem_stdU {v : Fin 3 → K} : v ∈ stdU ↔ v 2 = 0 := Iff.rfl
@[simp] theorem mem_stdR {v : Fin 3 → K} : v ∈ stdR ↔ v 0 = 0 ∧ v 1 = 0 := Iff.rfl

@[expose] def upperRadical : Subgroup (SL(3, K)) :=
  (unipotentRadical (stdU (K := K))).comap SpecialLinearGroup.toGL

@[expose] def lowerRadical : Subgroup (SL(3, K)) :=
  (unipotentRadical (stdR (K := K))).comap SpecialLinearGroup.toGL

theorem blockMat_inj {A A' : Matrix (Fin 2) (Fin 2) K} {b b' c c' : Fin 2 → K} {d d' : K} :
    blockMat A b c d = blockMat A' b' c' d' ↔ A = A' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h02 := congrFun (congrFun h 0) 2
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    have h12 := congrFun (congrFun h 1) 2
    have h20 := congrFun (congrFun h 2) 0
    have h21 := congrFun (congrFun h 2) 1
    have h22 := congrFun (congrFun h 2) 2
    have hA : A = A' := by
      ext i j
      fin_cases i <;> fin_cases j
      · simpa [blockMat] using h00
      · simpa [blockMat] using h01
      · simpa [blockMat] using h10
      · simpa [blockMat] using h11
    have hb : b = b' := by
      funext i
      fin_cases i
      · simpa [blockMat] using h02
      · simpa [blockMat] using h12
    have hc : c = c' := by
      funext j
      fin_cases j
      · simpa [blockMat] using h20
      · simpa [blockMat] using h21
    have hd : d = d' := by simpa [blockMat] using h22
    exact ⟨hA, hb, hc, hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

@[expose] def upperElem (b : Fin 2 → K) : SL(3, K) :=
  ⟨blockMat (1 : Matrix (Fin 2) (Fin 2) K) b 0 1, blockMat_det_upper b⟩

@[expose] def lowerElem (c : Fin 2 → K) : SL(3, K) :=
  ⟨blockMat (1 : Matrix (Fin 2) (Fin 2) K) 0 c 1, blockMat_det_lower c⟩

@[simp] theorem upperElem_zero : upperElem (0 : Fin 2 → K) = 1 := by
  apply Subtype.ext
  exact blockMat_one

@[simp] theorem lowerElem_zero : lowerElem (0 : Fin 2 → K) = 1 := by
  apply Subtype.ext
  exact blockMat_one

theorem upperElem_injective : Function.Injective (upperElem : (Fin 2 → K) → SL(3, K)) := by
  intro b b' h
  have h' : blockMat (1 : Matrix (Fin 2) (Fin 2) K) b 0 1 =
      blockMat (1 : Matrix (Fin 2) (Fin 2) K) b' 0 1 := congrArg Subtype.val h
  funext i
  fin_cases i
  · simpa using congrFun (congrFun h' 0) 2
  · simpa using congrFun (congrFun h' 1) 2

theorem lowerElem_injective : Function.Injective (lowerElem : (Fin 2 → K) → SL(3, K)) := by
  intro c c' h
  have h' : blockMat (1 : Matrix (Fin 2) (Fin 2) K) 0 c 1 =
      blockMat (1 : Matrix (Fin 2) (Fin 2) K) 0 c' 1 := congrArg Subtype.val h
  funext i
  fin_cases i
  · simpa using congrFun (congrFun h' 2) 0
  · simpa using congrFun (congrFun h' 2) 1

theorem upperElem_mul (b b' : Fin 2 → K) :
    upperElem b * upperElem b' = upperElem (b + b') := by
  apply Subtype.ext
  change blockMat (1 : Matrix (Fin 2) (Fin 2) K) b 0 1 *
      blockMat (1 : Matrix (Fin 2) (Fin 2) K) b' 0 1 =
    blockMat (1 : Matrix (Fin 2) (Fin 2) K) (b + b') 0 1
  rw [blockMat_mul, blockMat_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec]
  · funext i
    simp [Pi.add_apply, add_comm]
  · funext j
    simp
  · simp [zero_dotProduct]

theorem lowerElem_mul (c c' : Fin 2 → K) :
    lowerElem c * lowerElem c' = lowerElem (c + c') := by
  apply Subtype.ext
  change blockMat (1 : Matrix (Fin 2) (Fin 2) K) 0 c 1 *
      blockMat (1 : Matrix (Fin 2) (Fin 2) K) 0 c' 1 =
    blockMat (1 : Matrix (Fin 2) (Fin 2) K) 0 (c + c') 1
  rw [blockMat_mul, blockMat_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec]
  · funext i
    simp
  · funext j
    simp [Pi.add_apply, add_comm]
  · simp [zero_dotProduct]

theorem upperElem_inv (b : Fin 2 → K) : (upperElem b)⁻¹ = upperElem (-b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [upperElem_mul, add_neg_cancel, upperElem_zero]

theorem lowerElem_inv (c : Fin 2 → K) : (lowerElem c)⁻¹ = lowerElem (-c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [lowerElem_mul, add_neg_cancel, lowerElem_zero]

theorem mem_upperRadical_iff {g : SL(3, K)} :
    g ∈ upperRadical ↔ ∃ b : Fin 2 → K, g = upperElem b := by
  constructor
  · intro hg
    rw [upperRadical, Subgroup.mem_comap, mem_unipotentRadical_iff] at hg
    have hcol0 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1) = Pi.single 0 1 := by
      simpa using hg.2 (Pi.single 0 (1 : K)) (by simp [stdU])
    have hcol1 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 1 1) = Pi.single 1 1 := by
      simpa using hg.2 (Pi.single 1 (1 : K)) (by simp [stdU])
    have hthird : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 1) - Pi.single 2 1 ∈ stdU :=
      hg.1 (Pi.single 2 1)
    have h22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      have hthird2 := (mem_stdU.mp hthird)
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using sub_eq_zero.mp hthird2
    have h00 : (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
      have := congrFun hcol0 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have h10 : (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
      have := congrFun hcol0 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
      have := congrFun hcol0 2
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have h01 : (g : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
      have := congrFun hcol1 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have h11 : (g : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
      have := congrFun hcol1 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have h21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
      have := congrFun hcol1 2
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    refine ⟨fun i => (g : Matrix (Fin 3) (Fin 3) K) i.castSucc 2, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperElem, blockMat, h00, h10, h20, h01, h11, h21, h22]
  · rintro ⟨b, rfl⟩
    rw [upperRadical, Subgroup.mem_comap, mem_unipotentRadical_iff]
    constructor
    · intro x
      show ((SpecialLinearGroup.toGL (upperElem b) : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x) 2 = 0
      rw [SpecialLinearGroup.coe_GL_coe_matrix]
      simp [upperElem, blockMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro x hx
      simp only [mem_stdU] at hx
      rw [SpecialLinearGroup.coe_GL_coe_matrix]
      funext i
      fin_cases i <;>
        simp [upperElem, blockMat, hx, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mem_lowerRadical_iff {g : SL(3, K)} :
    g ∈ lowerRadical ↔ ∃ c : Fin 2 → K, g = lowerElem c := by
  constructor
  · intro hg
    rw [lowerRadical, Subgroup.mem_comap, mem_unipotentRadical_iff] at hg
    have hcol2 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 1) = Pi.single 2 1 := by
      simpa using hg.2 (Pi.single 2 (1 : K)) (by simp [stdR])
    have h02 : (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
      have := congrFun hcol2 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have h12 : (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
      have := congrFun hcol2 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have h22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      have := congrFun hcol2 2
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have hdiff0 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1) - Pi.single 0 1 ∈ stdR :=
      hg.1 (Pi.single 0 1)
    have hdiff1 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 1 1) - Pi.single 1 1 ∈ stdR :=
      hg.1 (Pi.single 1 1)
    have h00 : (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
      have h0 := (mem_stdR.mp hdiff0).1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using sub_eq_zero.mp h0
    have h01 : (g : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
      have h1 := (mem_stdR.mp hdiff1).1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h1
    have h10 : (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
      have h0 := (mem_stdR.mp hdiff0).2
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
    have h11 : (g : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
      have h1 := (mem_stdR.mp hdiff1).2
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using sub_eq_zero.mp h1
    refine ⟨fun j => (g : Matrix (Fin 3) (Fin 3) K) 2 j.castSucc, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerElem, blockMat, h00, h01, h02, h10, h11, h12, h22]
  · rintro ⟨c, rfl⟩
    rw [lowerRadical, Subgroup.mem_comap, mem_unipotentRadical_iff]
    constructor
    · intro x
      constructor
      · show ((SpecialLinearGroup.toGL (lowerElem c) : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x) 0 = 0
        rw [SpecialLinearGroup.coe_GL_coe_matrix]
        simp [lowerElem, blockMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      · show ((SpecialLinearGroup.toGL (lowerElem c) : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x) 1 = 0
        rw [SpecialLinearGroup.coe_GL_coe_matrix]
        simp [lowerElem, blockMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro x hx
      rcases hx with ⟨hx0, hx1⟩
      rw [SpecialLinearGroup.coe_GL_coe_matrix]
      funext i
      fin_cases i <;>
        simp [lowerElem, blockMat, hx0, hx1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
@[expose] noncomputable def levi : Subgroup (SL(3, K)) := (embSL (K := K)).range

theorem embSL_coe_blockMat (A : GL (Fin 2) K) :
    ((embSL A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      blockMat (A : Matrix (Fin 2) (Fin 2) K) 0 0
        ((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹ :=
  embSL_coe A

theorem mem_levi_iff {g : SL(3, K)} :
    g ∈ levi ↔ ∃ A : GL (Fin 2) K, g = embSL A := by
  change g ∈ (embSL (K := K)).range ↔ ∃ A : GL (Fin 2) K, g = embSL A
  exact ⟨fun ⟨A, hA⟩ => ⟨A, hA.symm⟩, fun ⟨A, hA⟩ => ⟨A, hA.symm⟩⟩

theorem embSL_inv_coe_blockMat (A : GL (Fin 2) K) :
    (((embSL A)⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      blockMat (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0
        ((A : Matrix (Fin 2) (Fin 2) K).det) := by
  have hdetinv : ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det) =
      ((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹ := by
    rw [← Matrix.GeneralLinearGroup.val_inv_det_apply A, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply A]
  rw [show (embSL A)⁻¹ = embSL A⁻¹ from (map_inv embSL A).symm, embSL_coe_blockMat,
    hdetinv, inv_inv]

theorem levi_blockc_eq_zero {g : SL(3, K)} (hg : g ∈ levi) :
    blockc (g : Matrix (Fin 3) (Fin 3) K) = 0 := by
  rw [mem_levi_iff] at hg
  obtain ⟨A, rfl⟩ := hg
  rw [embSL_coe_blockMat]
  funext j
  fin_cases j <;> simp [blockMat]

theorem levi_transvection_zero_one (t : K) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t ∈ levi := by
  let A : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.transvection (i := (0 : Fin 2)) (j := (1 : Fin 2)) t)
    (by
      have h : (Matrix.transvection (i := (0 : Fin 2)) (j := (1 : Fin 2)) t).det = 1 :=
        Matrix.det_transvection_of_ne (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (show (0 : Fin 2) ≠ 1 by decide) t
      rw [h]
      exact one_ne_zero)
  have hdet : ((A : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    dsimp [A]
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact Matrix.det_transvection_of_ne (i := (0 : Fin 2)) (j := (1 : Fin 2))
      (show (0 : Fin 2) ≠ 1 by decide) t
  have hdet2 : (1 + Matrix.of (fun i' j' =>
      if (0 : Fin 2) = i' ∧ (1 : Fin 2) = j' then t else 0) :
      Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [show (1 + Matrix.of (fun i' j' =>
        if (0 : Fin 2) = i' ∧ (1 : Fin 2) = j' then t else 0) :
        Matrix (Fin 2) (Fin 2) K) =
        Matrix.transvection (i := (0 : Fin 2)) (j := (1 : Fin 2)) t by
      ext i' j'
      simp [Matrix.transvection, Matrix.single]]
    exact Matrix.det_transvection_of_ne (i := (0 : Fin 2)) (j := (1 : Fin 2))
      (show (0 : Fin 2) ≠ 1 by decide) t
  change SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t ∈
    (embSL (K := K)).range
  refine MonoidHom.mem_range.mpr ⟨A, ?_⟩
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply, embSL_coe_blockMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, A, hdet, hdet2, Matrix.transvection, Matrix.single,
      Matrix.SpecialLinearGroup.transvection_coe]

theorem levi_transvection_one_zero (t : K) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t ∈ levi := by
  let A : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.transvection (i := (1 : Fin 2)) (j := (0 : Fin 2)) t)
    (by
      have h : (Matrix.transvection (i := (1 : Fin 2)) (j := (0 : Fin 2)) t).det = 1 :=
        Matrix.det_transvection_of_ne (i := (1 : Fin 2)) (j := (0 : Fin 2))
          (show (1 : Fin 2) ≠ 0 by decide) t
      rw [h]
      exact one_ne_zero)
  have hdet : ((A : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    dsimp [A]
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact Matrix.det_transvection_of_ne (i := (1 : Fin 2)) (j := (0 : Fin 2))
      (show (1 : Fin 2) ≠ 0 by decide) t
  have hdet2 : (1 + Matrix.of (fun i' j' =>
      if (1 : Fin 2) = i' ∧ (0 : Fin 2) = j' then t else 0) :
      Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [show (1 + Matrix.of (fun i' j' =>
        if (1 : Fin 2) = i' ∧ (0 : Fin 2) = j' then t else 0) :
        Matrix (Fin 2) (Fin 2) K) =
        Matrix.transvection (i := (1 : Fin 2)) (j := (0 : Fin 2)) t by
      ext i' j'
      simp [Matrix.transvection, Matrix.single]]
    exact Matrix.det_transvection_of_ne (i := (1 : Fin 2)) (j := (0 : Fin 2))
      (show (1 : Fin 2) ≠ 0 by decide) t
  change SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t ∈
    (embSL (K := K)).range
  refine MonoidHom.mem_range.mpr ⟨A, ?_⟩
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply, embSL_coe_blockMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, A, hdet, hdet2, Matrix.transvection, Matrix.single,
      Matrix.SpecialLinearGroup.transvection_coe]

@[expose] def negDiagElem : SL(3, K) :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

@[simp] theorem negDiagElem_coe :
    ((negDiagElem : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := rfl

theorem negDiagElem_mul_self : negDiagElem (K := K) * negDiagElem = 1 := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negDiagElem_coe, Matrix.mul_apply, Fin.sum_univ_three]

theorem negDiagElem_inv : (negDiagElem (K := K))⁻¹ = negDiagElem (K := K) :=
  inv_eq_of_mul_eq_one_right negDiagElem_mul_self

theorem negDiag_mem_levi : negDiagElem (K := K) ∈ levi := by
  change negDiagElem (K := K) ∈ (embSL (K := K)).range
  let A : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) (by simp [Matrix.det_fin_two])
  refine MonoidHom.mem_range.mpr ⟨A, ?_⟩
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply, embSL_coe_blockMat]
  change blockMat (A : Matrix (Fin 2) (Fin 2) K) 0 0
      ((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹ =
    ((negDiagElem (K := K) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, negDiagElem_coe, A,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

end CFSG.LinearAlgebra.SLThreeLevi
