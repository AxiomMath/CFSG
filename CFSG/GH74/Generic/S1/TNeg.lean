module

public import CFSG.GH74.Generic.S1.SymBlocksLinDefs
public import CFSG.GH74.Generic.S1.SymBlocksUniOps

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup

variable {F : Type} [Field F]

@[expose] def W01 : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem det_W01 : (W01 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [W01, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem isBlockAt_W01 : IsBlockAt 0 1 (W01 : Matrix (Fin 4) (Fin 4) F) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [W01] at hij ⊢

theorem eq_zDiag_of_comm (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 4) (Fin 4) F}
    (hblk : IsBlockAt 0 1 M) (hMM : M * M = 1) (hM1 : M ≠ 1) (hdet : M.det = 1)
    (hcomm : M * W01 = W01 * M) : M = Matrix.diagonal ![-1, -1, 1, 1] := by
  have hout : ∀ i j : Fin 4, ¬ ((i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1)) →
      M i j = if i = j then 1 else 0 := fun i j h => by
    simpa [Matrix.one_apply] using hblk i j h
  have e02 : M 0 2 = 0 := by simpa using hout 0 2 (by decide)
  have e03 : M 0 3 = 0 := by simpa using hout 0 3 (by decide)
  have e12 : M 1 2 = 0 := by simpa using hout 1 2 (by decide)
  have e13 : M 1 3 = 0 := by simpa using hout 1 3 (by decide)
  have e20 : M 2 0 = 0 := by simpa using hout 2 0 (by decide)
  have e21 : M 2 1 = 0 := by simpa using hout 2 1 (by decide)
  have e30 : M 3 0 = 0 := by simpa using hout 3 0 (by decide)
  have e31 : M 3 1 = 0 := by simpa using hout 3 1 (by decide)
  have e22 : M 2 2 = 1 := by simpa using hout 2 2 (by decide)
  have e33 : M 3 3 = 1 := by simpa using hout 3 3 (by decide)
  have e23 : M 2 3 = 0 := by simpa using hout 2 3 (by decide)
  have e32 : M 3 2 = 0 := by simpa using hout 3 2 (by decide)
  have hM : M = !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e02, e03, e12, e13, e20, e21, e30, e31, e22, e33, e23, e32]
  set a := M 0 0 with ha
  set b := M 0 1 with hb
  set c := M 1 0 with hc
  set d := M 1 1 with hd
  have hc00 := congrFun (congrFun hcomm 0) 0
  have hc01 := congrFun (congrFun hcomm 0) 1
  rw [hM] at hc00 hc01 hMM hdet
  simp [Matrix.mul_apply, Fin.sum_univ_succ, W01] at hc00 hc01
  have hm00 := congrFun (congrFun hMM 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at hm00
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove] at hdet
  have hda : d = a := hc01.symm
  have hcb : c = -b := by linear_combination hc00
  have hbb : (2 : F) * (b * b) = 0 := by
    rw [hda, hcb] at hdet
    rw [hcb] at hm00
    linear_combination hdet - hm00
  have hb0 : b = 0 := by
    have h1 : b * b = 0 := (mul_eq_zero.1 hbb).resolve_left h2
    exact mul_self_eq_zero.1 h1
  have hc0 : c = 0 := by rw [hcb, hb0, neg_zero]
  have haa : a * a = 1 := by
    rw [hb0] at hm00
    linear_combination hm00
  rcases mul_self_eq_one_iff.1 haa with h1 | h1
  · exfalso
    apply hM1
    rw [hM, hb0, hc0, hda, h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [hM, hb0, hc0, hda, h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem isBlockAt_neg_one_mul_zDiag :
    IsBlockAt 2 3 ((-1 : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal ![-1, -1, 1, 1]) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

section Lin

variable [Finite F]

omit [Finite F] in
theorem exists_W01_mem_blkLin : ∃ w : ↥(StatedSL 4 F), w ∈ blkLin (F := F) 0 1 ∧
    ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = W01 := by
  have hne : (W01 : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by rw [det_W01]; exact one_ne_zero
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero W01 hne, ?_⟩, ?_, rfl⟩
  · rw [statedSL_eq_detOne, mem_detOne]
    exact det_W01
  · exact isBlockAt_W01

theorem lin_neg_mul (hF : Nat.card F % 4 = 3) :
    ∀ s z : ↥(StatedSL 4 F), s ∈ Subgroup.center ↥(StatedSL 4 F) → s * s = 1 → s ≠ 1 →
      z ∈ blkLin (F := F) 0 1 → z * z = 1 → z ≠ 1 → (∀ g ∈ blkLin (F := F) 0 1, g * z = z * g) →
        s * z ∈ blkLin (F := F) 2 3 := by
  intro s z hsc hs2 hs1 hz hzz hz1 hzc
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  have hs : (s : GL (Fin 4) F) = -1 := by
    rcases (mem_center_statedSL_four_iff hF s).1 hsc with h | h
    · exact absurd (Subtype.ext h) hs1
    · rw [h, xGL_eq_neg_one]
  have hMs : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := by rw [hs]; simp
  obtain ⟨w, hw, hwM⟩ := exists_W01_mem_blkLin (F := F)
  have hMz : ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![-1, -1, 1, 1] := by
    apply eq_zDiag_of_comm h2 (mem_blkLin.1 hz)
    · have := congrArg (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hzz
      simpa using this
    · exact fun h => hz1 (Subtype.ext (Units.ext (by simpa using h)))
    · have : (z : GL (Fin 4) F) ∈ detOne F 4 := by
        rw [← statedSL_eq_detOne]
        exact z.2
      exact mem_detOne.1 this
    · have := congrArg (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
        (hzc w hw)
      simp only [Subgroup.coe_mul, Units.val_mul, hwM] at this
      exact this.symm
  rw [mem_blkLin, Subgroup.coe_mul, Units.val_mul, hMs, hMz]
  exact isBlockAt_neg_one_mul_zDiag

end Lin

section Uni

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)

include hF in
theorem exists_W01_mem_uniBlk : ∃ w : ↥(StatedSU 4 (p ^ f) F),
    w ∈ SymBlocksUni.uniBlk F (p ^ f) 0 1 ∧ ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = W01 := by
  have hne : (W01 : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by rw [det_W01]; exact one_ne_zero
  have hU : conjTr (unitaryInvolution F p f) (W01 : Matrix (Fin 4) (Fin 4) F) * W01 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr, W01, Matrix.mul_apply, Fin.sum_univ_succ]
  let g : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero W01 hne
  have hg : g ∈ SUid (unitaryInvolution F p f) 4 := ⟨det_W01, hU⟩
  have hgS : g ∈ StatedSU 4 (p ^ f) F := by
    rw [← SUid_eq_statedSU hF]
    exact hg
  refine ⟨⟨g, hgS⟩, ?_, rfl⟩
  rw [SymBlocksUni.mem_uniBlk_iff hF]
  exact isBlockAt_W01

include hF in
theorem uni_neg_mul (hq : p ^ f % 4 = 1) :
    ∀ s z : ↥(StatedSU 4 (p ^ f) F), s ∈ Subgroup.center ↥(StatedSU 4 (p ^ f) F) → s * s = 1 →
      s ≠ 1 → z ∈ SymBlocksUni.uniBlk F (p ^ f) 0 1 → z * z = 1 → z ≠ 1 →
        (∀ g ∈ SymBlocksUni.uniBlk F (p ^ f) 0 1, g * z = z * g) →
          s * z ∈ SymBlocksUni.uniBlk F (p ^ f) 2 3 := by
  intro s z hsc hs2 hs1 hz hzz hz1 hzc
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hs : (s : GL (Fin 4) F) = -1 := by
    rcases (mem_center_statedSU_four_iff hF hq s).1 hsc with h | h
    · exact absurd (Subtype.ext h) hs1
    · rw [h, xGL_eq_neg_one]
  have hMs : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := by rw [hs]; simp
  obtain ⟨w, hw, hwM⟩ := exists_W01_mem_uniBlk hF
  have hMz : ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![-1, -1, 1, 1] := by
    apply eq_zDiag_of_comm h2 ((SymBlocksUni.mem_uniBlk_iff hF).1 hz)
    · have := congrArg (fun x : ↥(StatedSU 4 (p ^ f) F) =>
        ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hzz
      simpa using this
    · exact fun h => hz1 (Subtype.ext (Units.ext (by simpa using h)))
    · exact (SymBlocksUni.unitary_of_mem_statedSU hF z).1
    · have := congrArg (fun x : ↥(StatedSU 4 (p ^ f) F) =>
        ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) (hzc w hw)
      simp only [Subgroup.coe_mul, Units.val_mul, hwM] at this
      exact this.symm
  rw [SymBlocksUni.mem_uniBlk_iff hF, Subgroup.coe_mul, Units.val_mul, hMs, hMz]
  exact isBlockAt_neg_one_mul_zDiag

end Uni

end CFSG.GH74.Generic.S1
