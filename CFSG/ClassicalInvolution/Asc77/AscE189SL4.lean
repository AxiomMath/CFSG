module

public import CFSG.ClassicalInvolution.Asc77.AscE189Sp4
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSL

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Blocks

variable {F : Type} [Field F]

theorem two_le_four : (2 : ℕ) ≤ 4 := by norm_num

theorem negBlock_four_zero : negBlock F 4 0 = Matrix.diagonal ![(-1 : F), -1, 1, 1] := by
  rw [negBlock_eq_diagonal]
  congr 1
  funext a
  fin_cases a <;> simp

theorem coe_blockSL_four_zero (A : SL(2, F)) :
    ((blockSL F 4 2 0 (by norm_num) A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

theorem coe_blockSL_four_two (A : SL(2, F)) :
    ((blockSL F 4 2 2 (by norm_num) A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

end Blocks


section Core

variable {F : Type} [Field F]

structure Sl4Ent (A : Matrix (Fin 4) (Fin 4) F) : Prop where
  z00 : A 0 0 = 0
  z01 : A 0 1 = 0
  z10 : A 1 0 = 0
  z11 : A 1 1 = 0
  z22 : A 2 2 = 0
  z23 : A 2 3 = 0
  z32 : A 3 2 = 0
  z33 : A 3 3 = 0
  r00 : A 0 2 * A 2 0 + A 0 3 * A 3 0 = -1
  r01 : A 0 2 * A 2 1 + A 0 3 * A 3 1 = 0
  r10 : A 1 2 * A 2 0 + A 1 3 * A 3 0 = 0
  r11 : A 1 2 * A 2 1 + A 1 3 * A 3 1 = -1

theorem sl4Ent_of (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 4) (Fin 4) F} (hAA : A * A = -1)
    (hAD : A * Matrix.diagonal ![(-1 : F), -1, 1, 1] =
      -(Matrix.diagonal ![(-1 : F), -1, 1, 1] * A)) : Sl4Ent A := by
  have key : ∀ i j, (![(-1 : F), -1, 1, 1] i + ![(-1 : F), -1, 1, 1] j) * A i j = 0 := by
    intro i j
    have h := congrFun (congrFun hAD i) j
    simp only [Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul] at h
    linear_combination h
  have hne : (-1 : F) + -1 ≠ 0 := by
    intro h
    apply h2
    linear_combination -h
  have hne' : (1 : F) + 1 ≠ 0 := by
    intro h
    apply h2
    linear_combination h
  have z00 : A 0 0 = 0 := (mul_eq_zero.mp (key 0 0)).resolve_left (by simpa using hne)
  have z01 : A 0 1 = 0 := (mul_eq_zero.mp (key 0 1)).resolve_left (by simpa using hne)
  have z10 : A 1 0 = 0 := (mul_eq_zero.mp (key 1 0)).resolve_left (by simpa using hne)
  have z11 : A 1 1 = 0 := (mul_eq_zero.mp (key 1 1)).resolve_left (by simpa using hne)
  refine ⟨z00, z01, z10, z11, (mul_eq_zero.mp (key 2 2)).resolve_left (by simpa using hne'),
    (mul_eq_zero.mp (key 2 3)).resolve_left (by simpa using hne'),
    (mul_eq_zero.mp (key 3 2)).resolve_left (by simpa using hne'),
    (mul_eq_zero.mp (key 3 3)).resolve_left (by simpa using hne'), ?_, ?_, ?_, ?_⟩
  · have h := congrFun (congrFun hAA 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, z00, z01, z10] at h
    linear_combination h
  · have h := congrFun (congrFun hAA 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four, z00, z01, z11] at h
    linear_combination h
  · have h := congrFun (congrFun hAA 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, z00, z10, z11] at h
    linear_combination h
  · have h := congrFun (congrFun hAA 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four, z01, z10, z11] at h
    linear_combination h

@[expose] def sl4b (A : Matrix (Fin 4) (Fin 4) F) : F := A 0 2 * A 1 3 - A 0 3 * A 1 2

@[expose] def sl4c (A : Matrix (Fin 4) (Fin 4) F) : F := A 2 0 * A 3 1 - A 2 1 * A 3 0

@[expose] def sl4G (A : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, A 2 0, 0, -sl4b A * A 2 1; 0, A 3 0, 0, -sl4b A * A 3 1]

variable {A : Matrix (Fin 4) (Fin 4) F}

theorem Sl4Ent.bc (hE : Sl4Ent A) : sl4b A * sl4c A = 1 := by
  have : sl4b A * sl4c A = (A 0 2 * A 2 0 + A 0 3 * A 3 0) * (A 1 2 * A 2 1 + A 1 3 * A 3 1) -
      (A 0 2 * A 2 1 + A 0 3 * A 3 1) * (A 1 2 * A 2 0 + A 1 3 * A 3 0) := by
    unfold sl4b sl4c
    ring
  rw [this, hE.r00, hE.r11, hE.r01, hE.r10]
  ring

theorem Sl4Ent.det_G (hE : Sl4Ent A) : (sl4G A).det = 1 := by
  have hbc : sl4b A * (A 2 0 * A 3 1 - A 2 1 * A 3 0) = 1 := hE.bc
  rw [sl4G, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  linear_combination hbc

theorem Sl4Ent.mul_G (hE : Sl4Ent A) :
    A * sl4G A = sl4G A * !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, sl4b A; 0, 0, -sl4c A, 0] := by
  have hbc : sl4b A * sl4c A = 1 := hE.bc
  have hbc' : sl4b A * (A 2 0 * A 3 1 - A 2 1 * A 3 0) = 1 := hbc
  obtain ⟨z00, z01, z10, z11, z22, z23, z32, z33, r00, r01, r10, r11⟩ := hE
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl4G, Matrix.mul_apply, Fin.sum_univ_four, z00, z01, z10, z11, z22, z23, z32, z33]
  · linear_combination r00
  · linear_combination (-sl4b A) * r01
  · linear_combination r10
  · linear_combination (-sl4b A) * r11
  · linear_combination (-A 2 1) * hbc
  · linear_combination (-A 3 1) * hbc

end Core

section Std

variable {F : Type} [Field F]

theorem e189SL4_std (h2 : (2 : F) ≠ 0) {ζ a : SL(4, F)}
    (hζ : ζ ∈ Subgroup.center SL(4, F)) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1)
    (ha2 : a * a = ζ) (haz : a * rootInv F two_le_four * a⁻¹ = ζ * rootInv F two_le_four) :
    ∃ y α β : SL(4, F), α ∈ rootSL2 F two_le_four ∧ β ∈ conjSub a (rootSL2 F two_le_four) ∧
      α ^ 4 = 1 ∧ β ^ 4 = 1 ∧ y * a * y⁻¹ = α * β := by
  have hζm : (ζ : Matrix (Fin 4) (Fin 4) F) = -1 :=
    (eq_one_or_coe_eq_neg_one (by norm_num) hζ hζ2).resolve_left hζ1
  have hAA : (a : Matrix (Fin 4) (Fin 4) F) * a = -1 := by
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) ha2
    simpa [hζm] using this
  have hAD : (a : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal ![(-1 : F), -1, 1, 1] =
      -(Matrix.diagonal ![(-1 : F), -1, 1, 1] * a) := by
    have h' : a * rootInv F two_le_four = ζ * rootInv F two_le_four * a := by
      calc a * rootInv F two_le_four = a * rootInv F two_le_four * a⁻¹ * a := by group
        _ = ζ * rootInv F two_le_four * a := by rw [haz]
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) h'
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv, hζm, negBlock_four_zero] at this
    simpa only [neg_mul, one_mul] using this
  have hE := sl4Ent_of h2 hAA hAD
  set b : F := sl4b (a : Matrix (Fin 4) (Fin 4) F) with hb
  set cc : F := sl4c (a : Matrix (Fin 4) (Fin 4) F) with hcc'
  have hbc : b * cc = 1 := hE.bc
  have hGdet : (sl4G (a : Matrix (Fin 4) (Fin 4) F)).det = 1 := hE.det_G
  have hAG : (a : Matrix (Fin 4) (Fin 4) F) * sl4G (a : Matrix (Fin 4) (Fin 4) F) =
      sl4G (a : Matrix (Fin 4) (Fin 4) F) *
        !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, b; 0, 0, -cc, 0] := hE.mul_G
  have hcc : cc ≠ 0 := right_ne_zero_of_mul_eq_one hbc
  have hccb : cc⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hbc)
  have hneg1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  set g : SL(4, F) := ⟨sl4G (a : Matrix (Fin 4) (Fin 4) F), hGdet⟩ with hg
  set α : SL(4, F) := blockSL F 4 2 0 (by norm_num) (spA (-1) hneg1) with hα
  set β : SL(4, F) := blockSL F 4 2 2 (by norm_num) (spA cc hcc) with hβ
  have hαm : (α : Matrix (Fin 4) (Fin 4) F) =
      !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    rw [hα, coe_blockSL_four_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spA_apply_00, spA_apply_01, spA_apply_10, spA_apply_11]
  have hβm : (β : Matrix (Fin 4) (Fin 4) F) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, b; 0, 0, -cc, 0] := by
    rw [hβ, coe_blockSL_four_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spA_apply_00, spA_apply_01, spA_apply_10, spA_apply_11, hccb]
  have hαβ : ((α * β : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, b; 0, 0, -cc, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hαm, hβm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have hag : a * g = g * (α * β) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hαβ]
    exact hAG
  refine ⟨g⁻¹, α, β, ⟨_, rfl⟩, ?_, ?_, ?_, ?_⟩
  · have hconj : conjSub a (rootSL2 F two_le_four) =
        longRootGroup (-(Matrix.diagonal ![(-1 : F), -1, 1, 1])) := by
      rw [rootSL2_eq_longRootGroup h2 two_le_four]
      show (longRootGroup (negBlock F 4 0)).map (MulAut.conj a).toMonoidHom = _
      rw [← longRootGroup_conj]
      congr 1
      rw [negBlock_four_zero]
      calc (a : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal ![(-1 : F), -1, 1, 1] *
            ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
          = -(Matrix.diagonal ![(-1 : F), -1, 1, 1] * a *
              ((a⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)) := by rw [hAD]; simp
        _ = -Matrix.diagonal ![(-1 : F), -1, 1, 1] := by
            rw [Matrix.mul_assoc, coe_mul_coe_inv, Matrix.mul_one]
    rw [hconj, mem_longRootGroup, hβm]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · rw [hα, ← map_pow, spA_pow_four, map_one]
  · rw [hβ, ← map_pow, spA_pow_four, map_one]
  · calc g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * (a * g) := by rw [inv_inv, mul_assoc]
      _ = α * β := by rw [hag, ← mul_assoc, inv_mul_cancel, one_mul]

end Std


section Model

variable {p e : ℕ} [Fact p.Prime]

theorem e189ModelAt_psl_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) : E189ModelAt p e .PSL 4 := by
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hfund : fundamentalSubgroups .PSL (modelUniv .PSL 4 p e Fact.out).D =
      {F | ∃ g : SL(4, GaloisField p e),
        F = conjSub g (rootSL2 (GaloisField p e) two_le_four)} := by
    refine (CFSG.ClassicalInvolution.RouteD.Exotic.fundamentalSubgroups_psl_eq (p := p) (f := e)
      (m := 3) (by norm_num)).trans ?_
    ext L
    exact mem_longRootSet_iff _
  have hcl := isClassicalSL2_rootSL2 h2 two_le_four
  have key : E189AtFam SL(4, GaloisField p e)
      {F | ∃ g : SL(4, GaloisField p e),
        F = conjSub g (rootSL2 (GaloisField p e) two_le_four)} :=
    e189AtFam_of_conjClass (isUniqueInvolution_of_isClassicalSL2 hcl hodd)
      (fun c hc => conjSub_eq_of_isClassicalSL2 hcl hc)
      (fun ζ hζ hζ1 hζ2 a ha2 haz => e189SL4_std h2 hζ hζ1 hζ2 ha2 haz)
  unfold E189ModelAt modelFund ModelGrp
  rw [hfund]
  exact key

end Model

end CFSG.ClassicalInvolution.Asc77
