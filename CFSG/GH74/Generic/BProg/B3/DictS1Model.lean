module

public import CFSG.GH74.Generic.BProg.B1.PilotS1Models
public import CFSG.GH74.Generic.S1.SymBlocksLinDefs
public import CFSG.GH74.L5U5.ModelsPairs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Generic CFSG.Assembly.LowTwoRank Matrix Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F]

namespace DictS1Model

theorem eq_blk4_left {M : Matrix (Fin 4) (Fin 4) F} (h : S1.IsBlockAt 0 1 M) :
    M = blk4 !![M 0 0, M 0 1; M 1 0, M 1 1] 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4_apply, e4_symm_zero, e4_symm_one, e4_symm_two, e4_symm_three] <;>
    rw [h] <;> simp [Matrix.one_apply]

theorem eq_blk4_right {M : Matrix (Fin 4) (Fin 4) F} (h : S1.IsBlockAt 2 3 M) :
    M = blk4 1 !![M 2 2, M 2 3; M 3 2, M 3 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4_apply, e4_symm_zero, e4_symm_one, e4_symm_two, e4_symm_three] <;>
    rw [h] <;> simp [Matrix.one_apply]

theorem isBlockAt_blk4_left (A : Matrix (Fin 2) (Fin 2) F) : S1.IsBlockAt 0 1 (blk4 A 1) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [blk4_apply, e4_symm_zero, e4_symm_one, e4_symm_two,
    e4_symm_three, Matrix.one_apply]

theorem isBlockAt_blk4_right (B : Matrix (Fin 2) (Fin 2) F) : S1.IsBlockAt 2 3 (blk4 1 B) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [blk4_apply, e4_symm_zero, e4_symm_one, e4_symm_two,
    e4_symm_three, Matrix.one_apply]

end DictS1Model

open DictS1Model in
theorem blkLin_zero_one_eq_J2 : S1.blkLin (F := F) 0 1 = (ModelData.lin F).J2 := by
  ext g
  constructor
  · intro hg
    have hg' : S1.IsBlockAt 0 1 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := hg
    set A : Matrix (Fin 2) (Fin 2) F :=
      !![((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 1;
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 0, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 1]
      with hA
    have hM : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 A 1 := eq_blk4_left hg'
    have hg1 : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      have h1 : (g : GL (Fin 4) F) ∈ detOne F 4 := by
        rw [← statedSL_eq_detOne]
        exact g.2
      exact h1
    have hdet : A.det = 1 := by
      have := congrArg Matrix.det hM
      rw [det_blk4, det_one, mul_one, hg1] at this
      exact this.symm
    let a : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact one_ne_zero)
    change (g : GL (Fin 4) F) ∈ (StatedSL 2 F).map (blkL F)
    refine ⟨a, ?_, ?_⟩
    · rw [SetLike.mem_coe]
      change (_ : GL (Fin 2) F) ∈ StatedSL 2 F
      rw [statedSL_eq_detOne, mem_detOne]
      exact hdet
    · apply Units.ext
      rw [blkL_apply, coe_diagGL, hM]
      rfl
  · intro hg
    have hg' : (g : GL (Fin 4) F) ∈ (StatedSL 2 F).map (blkL F) := hg
    obtain ⟨a, -, hga⟩ := hg'
    show S1.IsBlockAt 0 1 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [← hga, blkL_apply, coe_diagGL]
    exact isBlockAt_blk4_left _

open DictS1Model in
theorem blkLin_two_three_eq_J4 : S1.blkLin (F := F) 2 3 = (ModelData.lin F).J4 := by
  ext g
  constructor
  · intro hg
    have hg' : S1.IsBlockAt 2 3 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := hg
    set B : Matrix (Fin 2) (Fin 2) F :=
      !![((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 2 2, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 2 3;
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 2, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3]
      with hB
    have hM : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 1 B := eq_blk4_right hg'
    have hg1 : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      have h1 : (g : GL (Fin 4) F) ∈ detOne F 4 := by
        rw [← statedSL_eq_detOne]
        exact g.2
      exact h1
    have hdet : B.det = 1 := by
      have := congrArg Matrix.det hM
      rw [det_blk4, det_one, one_mul, hg1] at this
      exact this.symm
    let b : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero B (by rw [hdet]; exact one_ne_zero)
    change (g : GL (Fin 4) F) ∈ (StatedSL 2 F).map (blkR F)
    refine ⟨b, ?_, ?_⟩
    · rw [SetLike.mem_coe]
      change (_ : GL (Fin 2) F) ∈ StatedSL 2 F
      rw [statedSL_eq_detOne, mem_detOne]
      exact hdet
    · apply Units.ext
      rw [blkR_apply, coe_diagGL, hM]
      rfl
  · intro hg
    have hg' : (g : GL (Fin 4) F) ∈ (StatedSL 2 F).map (blkR F) := hg
    obtain ⟨b, -, hgb⟩ := hg'
    show S1.IsBlockAt 2 3 ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [← hgb, blkR_apply, coe_diagGL]
    exact isBlockAt_blk4_right _

theorem splitAt_blkLin [Finite F] (hF : Nat.card F % 4 = 3) :
    B1.PilotS1.SplitAt F (⊤ : Subgroup ↥(StatedSL 4 F)) (ModelData.lin F).xK (ModelData.lin F).yK
      (S1.blkLin (F := F) 0 1) (S1.blkLin (F := F) 2 3) := by
  have h2 : (2 : F) ≠ 0 := by
    have : Fintype F := Fintype.ofFinite F
    apply Ring.two_ne_zero
    intro hc
    have h0 := FiniteField.even_card_iff_char_two.1 hc
    rw [← Nat.card_eq_fintype_card] at h0
    omega
  have hsq : Nat.card F < 4 → ∀ c : F, c ≠ 0 → c * c = 1 := by
    intro h4 c hc
    have h3 : Nat.card F = 3 := by omega
    have : Fintype F := Fintype.ofFinite F
    have hpow := FiniteField.pow_card_sub_one_eq_one c hc
    rw [← Nat.card_eq_fintype_card, h3] at hpow
    simpa [pow_two] using hpow
  rw [blkLin_zero_one_eq_J2, blkLin_two_three_eq_J4]
  exact B1.PilotS1.splitAt_yK (ModelData.lin F) h2 (lin_sl2_equiv_H2 F) hsq

end CFSG.GH74.Generic.BProg.B3
