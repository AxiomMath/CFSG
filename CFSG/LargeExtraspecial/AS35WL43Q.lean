module

public import CFSG.LargeExtraspecial.AS35WBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks

public section

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.CatFactsL4U4

namespace AS35W

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Blocks

variable {R : Type} [CommRing R]

@[expose] def blkA (M : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

@[expose] def blkB (M : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 0 2, M 0 3; M 1 2, M 1 3]

@[expose] def blkC (M : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 2 0, M 2 1; M 3 0, M 3 1]

@[expose] def blkD (M : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 2 2, M 2 3; M 3 2, M 3 3]

theorem blkA_mul (M N : Matrix (Fin 4) (Fin 4) R) :
    blkA (M * N) = blkA M * blkA N + blkB M * blkC N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkA, blkB, blkC, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem blkB_mul (M N : Matrix (Fin 4) (Fin 4) R) :
    blkB (M * N) = blkA M * blkB N + blkB M * blkD N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkA, blkB, blkD, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem blkC_mul (M N : Matrix (Fin 4) (Fin 4) R) :
    blkC (M * N) = blkC M * blkA N + blkD M * blkC N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkA, blkC, blkD, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem blkD_mul (M N : Matrix (Fin 4) (Fin 4) R) :
    blkD (M * N) = blkC M * blkB N + blkD M * blkD N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkB, blkC, blkD, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem blk_one :
    blkA (1 : Matrix (Fin 4) (Fin 4) R) = 1 ∧ blkB (1 : Matrix (Fin 4) (Fin 4) R) = 0 ∧
      blkC (1 : Matrix (Fin 4) (Fin 4) R) = 0 ∧ blkD (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [blkA, blkB, blkC, blkD]

omit [CommRing R] in
theorem blk_ext {M N : Matrix (Fin 4) (Fin 4) R} (hA : blkA M = blkA N) (hB : blkB M = blkB N)
    (hC : blkC M = blkC N) (hD : blkD M = blkD N) : M = N := by
  ext i j
  have eA := fun a b => congrFun (congrFun hA a) b
  have eB := fun a b => congrFun (congrFun hB a) b
  have eC := fun a b => congrFun (congrFun hC a) b
  have eD := fun a b => congrFun (congrFun hD a) b
  simp only [blkA, blkB, blkC, blkD] at eA eB eC eD
  fin_cases i <;> fin_cases j
  exacts [eA 0 0, eA 0 1, eB 0 0, eB 0 1, eA 1 0, eA 1 1, eB 1 0, eB 1 1,
    eC 0 0, eC 0 1, eD 0 0, eD 0 1, eC 1 0, eC 1 1, eD 1 0, eD 1 1]

@[expose] def det2 (a : Matrix (Fin 2) (Fin 2) R) : R := a 0 0 * a 1 1 - a 0 1 * a 1 0

theorem det2_mul (a b : Matrix (Fin 2) (Fin 2) R) : det2 (a * b) = det2 a * det2 b := by
  simp [det2, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem det2_one : det2 (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp [det2]

end Blocks

@[expose] def q8List : List (Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  [1, -1, !![0, 1; -1, 0], !![0, -1; 1, 0], !![1, 1; 1, -1], !![-1, -1; -1, 1],
    !![1, -1; -1, -1], !![-1, 1; 1, 1]]

set_option maxRecDepth 20000 in
theorem q8List_mul : ∀ a ∈ q8List, ∀ b ∈ q8List, a * b ∈ q8List := by
  decide

set_option maxRecDepth 20000 in
theorem q8List_prop : ∀ a ∈ q8List, det2 a = 1 ∧ a * a * (a * a) = 1 := by
  decide

public theorem q8_inv {a : SpecialLinearGroup (Fin 2) (ZMod 3)}
    (ha : (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∈ q8List) : a⁻¹ = a * a * a := by
  have h := (q8List_prop (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ha).2
  have h' : a * (a * a * a) = 1 := by
    apply Subtype.ext
    show (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * ((a : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (a : Matrix (Fin 2) (Fin 2) (ZMod 3))) = 1
    calc (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * ((a : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (a : Matrix (Fin 2) (Fin 2) (ZMod 3)))
        = (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (a : Matrix (Fin 2) (Fin 2) (ZMod 3))) := by
          noncomm_ring
      _ = 1 := h
  exact inv_eq_of_mul_eq_one_right h'

set_option maxRecDepth 20000 in
theorem mem_q8List_of : ∀ a : Matrix (Fin 2) (Fin 2) (ZMod 3), det2 a = 1 →
    a * a * (a * a) = 1 → a ∈ q8List := by
  decide

theorem conj_mem_q8List {P P' a : Matrix (Fin 2) (Fin 2) (ZMod 3)} (hPP : P * P' = 1)
    (hPP' : P' * P = 1) (ha : a ∈ q8List) : P * a * P' ∈ q8List := by
  obtain ⟨hd, h4⟩ := q8List_prop a ha
  refine mem_q8List_of _ ?_ ?_
  · rw [det2_mul, det2_mul, hd, mul_one, ← det2_mul, hPP, det2_one]
  · calc P * a * P' * (P * a * P') * (P * a * P' * (P * a * P')) =
        P * (a * (P' * P) * a * (P' * P) * a * (P' * P) * a) * P' := by
          simp only [Matrix.mul_assoc]
      _ = P * (a * a * (a * a)) * P' := by rw [hPP']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h4, Matrix.mul_one, hPP]

@[expose] def qtSet : Set (SpecialLinearGroup (Fin 4) (ZMod 3)) :=
  {g | blkB (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 0 ∧
    blkC (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 0 ∧
    blkA (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ q8List ∧
    blkD (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ q8List}

theorem qtSet_one : (1 : SpecialLinearGroup (Fin 4) (ZMod 3)) ∈ qtSet := by
  obtain ⟨h1, h2, h3, h4⟩ := blk_one (R := ZMod 3)
  change blkB (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 0 ∧
    blkC (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 0 ∧
    blkA (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ q8List ∧
    blkD (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ q8List
  refine ⟨h2, h3, ?_, ?_⟩
  · rw [h1]; simp [q8List]
  · rw [h4]; simp [q8List]

theorem qtSet_mul {g g' : SpecialLinearGroup (Fin 4) (ZMod 3)} (hg : g ∈ qtSet)
    (hg' : g' ∈ qtSet) : g * g' ∈ qtSet := by
  obtain ⟨hB, hC, hA, hD⟩ := hg
  obtain ⟨hB', hC', hA', hD'⟩ := hg'
  change blkB ((g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (g' : Matrix (Fin 4) (Fin 4) (ZMod 3))) =
      0 ∧
    blkC ((g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (g' : Matrix (Fin 4) (Fin 4) (ZMod 3))) = 0 ∧
    blkA ((g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (g' : Matrix (Fin 4) (Fin 4) (ZMod 3))) ∈
      q8List ∧
    blkD ((g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (g' : Matrix (Fin 4) (Fin 4) (ZMod 3))) ∈
      q8List
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [blkA_mul, blkB_mul, blkC_mul, blkD_mul, hB, hC, hB', hC', Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
  · exact q8List_mul _ hA _ hA'
  · exact q8List_mul _ hD _ hD'

theorem qtSet_pow4 {g : SpecialLinearGroup (Fin 4) (ZMod 3)} (hg : g ∈ qtSet) :
    g * g * (g * g) = 1 := by
  obtain ⟨hB, hC, hA, hD⟩ := hg
  obtain ⟨h1, h2, h3, h4⟩ := blk_one (R := ZMod 3)
  apply Subtype.ext
  change (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
    ((g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (g : Matrix (Fin 4) (Fin 4) (ZMod 3))) = 1
  refine blk_ext ?_ ?_ ?_ ?_ <;>
    simp only [blkA_mul, blkB_mul, blkC_mul, blkD_mul, hB, hC, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, h1, h2, h3, h4]
  · exact (q8List_prop _ hA).2
  · exact (q8List_prop _ hD).2

@[expose] def Qt : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 3)) where
  carrier := qtSet
  one_mem' := qtSet_one
  mul_mem' := qtSet_mul
  inv_mem' {g} hg := by
    have e : g⁻¹ = g * g * g := inv_eq_of_mul_eq_one_right (by
      rw [← qtSet_pow4 hg]
      group)
    rw [e]
    exact qtSet_mul (qtSet_mul hg hg) hg

@[expose] def dSL : SpecialLinearGroup (Fin 4) (ZMod 3) :=
  ⟨HBlocks.X1 1, by
    rw [HBlocks.X1, Matrix.det_succ_row_zero]
    norm_num [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]⟩

set_option maxRecDepth 20000 in
theorem blk_dSL : blkA (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 ∧
    blkB (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 0 ∧
    blkC (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 0 ∧
    blkD (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = -1 := by
  decide

theorem blk_neg {R : Type} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    blkA (-M) = -blkA M ∧ blkB (-M) = -blkB M ∧ blkC (-M) = -blkC M ∧ blkD (-M) = -blkD M := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [blkA, blkB, blkC, blkD]

theorem eq_zero_of_neg_eq {M : Matrix (Fin 2) (Fin 2) (ZMod 3)} (h : -M = M) : M = 0 := by
  have key : ∀ x : ZMod 3, -x = x → x = 0 := by decide
  ext i j
  exact key _ (congrFun (congrFun h i) j)

theorem mul_negOne (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) : N * -1 = -N := by
  rw [Matrix.mul_neg, Matrix.mul_one]

theorem negOne_mul (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) : -1 * N = -N := by
  rw [Matrix.neg_mul, Matrix.one_mul]

theorem blk_of_comm {M : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (h : (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * M = M * dSL) : blkB M = 0 ∧ blkC M = 0 := by
  obtain ⟨hA, hB, hC, hD⟩ := blk_dSL
  have eB := congrArg blkB h
  have eC := congrArg blkC h
  rw [blkB_mul, blkB_mul, hA, hB, hD, Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_zero,
    zero_add, mul_negOne] at eB
  rw [blkC_mul, blkC_mul, hA, hC, hD, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul,
    zero_add, negOne_mul] at eC
  exact ⟨eq_zero_of_neg_eq eB.symm, eq_zero_of_neg_eq eC⟩

theorem blk_of_anticomm {M : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (h : (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * M = -(M * dSL)) :
    blkA M = 0 ∧ blkD M = 0 := by
  obtain ⟨hA, hB, hC, hD⟩ := blk_dSL
  have eA := congrArg blkA h
  have eD := congrArg blkD h
  rw [(blk_neg (R := ZMod 3) _).1, blkA_mul, blkA_mul, hA, hB, hC, Matrix.one_mul,
    Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, add_zero] at eA
  rw [(blk_neg (R := ZMod 3) _).2.2.2, blkD_mul, blkD_mul, hB, hC, hD, Matrix.zero_mul,
    zero_add, Matrix.mul_zero, zero_add, mul_negOne, negOne_mul, neg_neg] at eD
  exact ⟨eq_zero_of_neg_eq eA.symm, eq_zero_of_neg_eq eD⟩

theorem coe_mul_inv {R : Type} [CommRing R] (h : SpecialLinearGroup (Fin 4) R) :
    (h : Matrix (Fin 4) (Fin 4) R) * ((h⁻¹ : SpecialLinearGroup (Fin 4) R) :
      Matrix (Fin 4) (Fin 4) R) = 1 ∧
    ((h⁻¹ : SpecialLinearGroup (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) *
      (h : Matrix (Fin 4) (Fin 4) R) = 1 :=
  ⟨congrArg Subtype.val (mul_inv_cancel h), congrArg Subtype.val (inv_mul_cancel h)⟩

theorem conj_mem_Qt {h g : SpecialLinearGroup (Fin 4) (ZMod 3)}
    (hh : (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * h = h * dSL ∨
      (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * h = -((h : Matrix (Fin 4) (Fin 4) (ZMod 3)) * dSL))
    (hg : g ∈ Qt) : h * g * h⁻¹ ∈ Qt := by
  obtain ⟨hB, hC, hA, hD⟩ := hg
  obtain ⟨h1, h2, h3, h4⟩ := blk_one (R := ZMod 3)
  obtain ⟨e1, e2⟩ := coe_mul_inv h
  set Hm : Matrix (Fin 4) (Fin 4) (ZMod 3) := (h : Matrix (Fin 4) (Fin 4) (ZMod 3)) with hHm
  set Hi : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
    ((h⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) with hHi
  set Dm : Matrix (Fin 4) (Fin 4) (ZMod 3) := (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) with hDm
  change blkB (Hm * (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * Hi) = 0 ∧
    blkC (Hm * (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * Hi) = 0 ∧
    blkA (Hm * (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * Hi) ∈ q8List ∧
    blkD (Hm * (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * Hi) ∈ q8List
  set G := (g : Matrix (Fin 4) (Fin 4) (ZMod 3))
  rcases hh with hh | hh
  · have hi : Dm * Hi = Hi * Dm := by
      calc Dm * Hi = Hi * Hm * Dm * Hi := by rw [e2, Matrix.one_mul]
        _ = Hi * (Dm * Hm) * Hi := by rw [hh]; simp only [Matrix.mul_assoc]
        _ = Hi * Dm * (Hm * Hi) := by simp only [Matrix.mul_assoc]
        _ = Hi * Dm := by rw [e1, Matrix.mul_one]
    obtain ⟨hhB, hhC⟩ := blk_of_comm hh
    obtain ⟨hiB, hiC⟩ := blk_of_comm hi
    have k1 := congrArg blkA e1
    have k2 := congrArg blkA e2
    have k3 := congrArg blkD e1
    have k4 := congrArg blkD e2
    rw [blkA_mul, hhB, Matrix.zero_mul, add_zero, h1] at k1
    rw [blkA_mul, hiB, Matrix.zero_mul, add_zero, h1] at k2
    rw [blkD_mul, hhC, Matrix.zero_mul, zero_add, h4] at k3
    rw [blkD_mul, hiC, Matrix.zero_mul, zero_add, h4] at k4
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [blkA_mul, blkB_mul, blkC_mul, blkD_mul, hhB, hhC, hiB, hiC, hB, hC,
        Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    · exact conj_mem_q8List k1 k2 hA
    · exact conj_mem_q8List k3 k4 hD
  · have hmd : Hm * Dm = -(Dm * Hm) := by rw [hh, neg_neg]
    have hi : Dm * Hi = -(Hi * Dm) := by
      calc Dm * Hi = Hi * Hm * Dm * Hi := by rw [e2, Matrix.one_mul]
        _ = Hi * (Hm * Dm) * Hi := by simp only [Matrix.mul_assoc]
        _ = Hi * (-(Dm * Hm)) * Hi := by rw [hmd]
        _ = -(Hi * Dm * (Hm * Hi)) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = -(Hi * Dm) := by rw [e1, Matrix.mul_one]
    obtain ⟨hhA, hhD⟩ := blk_of_anticomm hh
    obtain ⟨hiA, hiD⟩ := blk_of_anticomm hi
    have k1 := congrArg blkA e1
    have k2 := congrArg blkD e2
    have k3 := congrArg blkD e1
    have k4 := congrArg blkA e2
    rw [blkA_mul, hhA, Matrix.zero_mul, zero_add, h1] at k1
    rw [blkD_mul, hiD, Matrix.zero_mul, add_zero, h4] at k2
    rw [blkD_mul, hhD, Matrix.zero_mul, add_zero, h4] at k3
    rw [blkA_mul, hiA, Matrix.zero_mul, zero_add, h1] at k4
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [blkA_mul, blkB_mul, blkC_mul, blkD_mul, hhA, hhD, hiA, hiD, hB, hC,
        Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    · exact conj_mem_q8List k1 k2 hD
    · exact conj_mem_q8List k3 k4 hA

public theorem conj_mem_Qt_of_comm_or_anticomm {h g : SpecialLinearGroup (Fin 4) (ZMod 3)}
    (hh : (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * h = h * dSL ∨
      (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * h = -((h : Matrix (Fin 4) (Fin 4) (ZMod 3)) * dSL))
    (hg : g ∈ Qt) : h * g * h⁻¹ ∈ Qt :=
  conj_mem_Qt hh hg

public theorem comm_dSL_of_mem_Qt {g : SpecialLinearGroup (Fin 4) (ZMod 3)} (hg : g ∈ Qt) :
    g * dSL = dSL * g := by
  obtain ⟨hB, hC, hA, hD⟩ := hg
  obtain ⟨h1, h2, h3, h4⟩ := blk_dSL
  apply Subtype.ext
  refine blk_ext ?_ ?_ ?_ ?_ <;>
    simp [blkA_mul, blkB_mul, blkC_mul, blkD_mul, hB, hC, h1, h2, h3, h4]

@[expose] def tMat : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

@[expose] def cMat : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1]

@[expose] def tSL : SpecialLinearGroup (Fin 4) (ZMod 3) :=
  ⟨tMat, by
    rw [tMat, Matrix.det_succ_row_zero]
    norm_num [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]⟩

@[expose] def cSL : SpecialLinearGroup (Fin 4) (ZMod 3) :=
  ⟨cMat, by
    rw [cMat, Matrix.det_succ_row_zero]
    norm_num [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]⟩

theorem coe_mul4 {R : Type} [CommRing R] (g g' : SpecialLinearGroup (Fin 4) R) :
    ((g * g' : SpecialLinearGroup (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) =
      (g : Matrix (Fin 4) (Fin 4) R) * (g' : Matrix (Fin 4) (Fin 4) R) :=
  rfl

theorem coe_one4 {R : Type} [CommRing R] :
    ((1 : SpecialLinearGroup (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = 1 :=
  rfl

set_option maxRecDepth 20000 in
theorem mat_facts : (blkB (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 0 ∧
      blkC (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 0 ∧
      blkA (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ q8List ∧
      blkD (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ q8List) ∧
    (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      scalar (Fin 4) ((-1 : (ZMod 3)ˣ) : ZMod 3) ∧
    (cSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (cSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∧
    (cSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * ((cSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
      (cSL : Matrix (Fin 4) (Fin 4) (ZMod 3))) = 1 ∧
    (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (cSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
      (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      (cSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (cSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∧
    (tSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) 0 1 ≠ 0 ∧
    (cSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) 2 0 ≠ 0 ∧ (-1 : (ZMod 3)ˣ) ^ 4 = 1 := by
  decide

theorem units_three : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by decide

theorem entry_of_scalar {M : Matrix (Fin 4) (Fin 4) (ZMod 3)} {c : ZMod 3}
    (h : M = scalar (Fin 4) c) : M 0 1 = 0 ∧ M 2 0 = 0 := by
  rw [h, scalar_apply]
  simp

theorem proj_ne_one_of {g : SpecialLinearGroup (Fin 4) (ZMod 3)}
    (hg : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) 0 1 ≠ 0 ∨
      (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) 2 0 ≠ 0) : proj 4 (ZMod 3) g ≠ 1 := by
  intro h1
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
  obtain ⟨e1, e2⟩ := entry_of_scalar hc
  rcases hg with hg | hg
  · exact hg e1
  · exact hg e2

theorem false_of_u1 (hz : W2Data (projectiveSL 4 (ZMod 3)) (proj 4 (ZMod 3) dSL)) : False := by
  obtain ⟨⟨tB, tC, tA, tD⟩, tt, ct, c3, dcd, t01, c20, u4⟩ := mat_facts
  obtain ⟨dA, dB, dC, dD⟩ := blk_dSL
  set P : Subgroup (projectiveSL 4 (ZMod 3)) := Qt.map (proj 4 (ZMod 3))
  have hcommD : ∀ g ∈ Qt, g * dSL = dSL * g := by
    rintro g ⟨hB, hC, -, -⟩
    apply Subtype.ext
    change (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (g : Matrix (Fin 4) (Fin 4) (ZMod 3))
    refine blk_ext ?_ ?_ ?_ ?_ <;>
      simp only [blkA_mul, blkB_mul, blkC_mul, blkD_mul, hB, hC, dA, dB, dC, dD, Matrix.mul_one,
        Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, mul_negOne,
        negOne_mul]
  have hPC : P ≤ centralizer ({proj 4 (ZMod 3) dSL} : Set (projectiveSL 4 (ZMod 3))) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcommD g hg]
  have hPn : ∀ c ∈ centralizer ({proj 4 (ZMod 3) dSL} : Set (projectiveSL 4 (ZMod 3))),
      ∀ p ∈ P, c * p * c⁻¹ ∈ P := by
    intro c hc p hp
    obtain ⟨h, rfl⟩ := proj_surjective 4 (ZMod 3) c
    obtain ⟨g, hg, rfl⟩ := hp
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, proj_eq_proj_iff] at hc
    set X := (h * dSL)⁻¹ * (dSL * h) with hX
    obtain ⟨u, -, hu⟩ := mem_scalars.1 hc
    have e : dSL * h = h * dSL * X := by rw [hX]; group
    have e' := congrArg Subtype.val e
    change (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (h : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      (h : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
        (X : Matrix (Fin 4) (Fin 4) (ZMod 3)) at e'
    rw [hu, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at e'
    have hh : (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * h = h * dSL ∨
        (dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * h =
          -((h : Matrix (Fin 4) (Fin 4) (ZMod 3)) * dSL) := by
      rcases units_three u with rfl | rfl
      · left
        rw [e', Units.val_one, one_smul]
      · right
        rw [e', Units.val_neg, Units.val_one, neg_one_smul]
    exact ⟨h * g * h⁻¹, conj_mem_Qt hh hg, by rw [map_mul, map_mul, map_inv]⟩
  have hP2 : IsPGroup 2 P := by
    rintro ⟨x, g, hg, rfl⟩
    refine ⟨2, Subtype.ext ?_⟩
    change proj 4 (ZMod 3) g ^ 2 ^ 2 = 1
    have h4 : g ^ 2 ^ 2 = 1 := by
      rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, sq]
      exact qtSet_pow4 hg
    rw [← map_pow, h4, map_one]
  have htP : proj 4 (ZMod 3) tSL ∈ P := ⟨tSL, ⟨tB, tC, tA, tD⟩, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht2 : orderOf (proj 4 (ZMod 3) tSL) = 2 := by
    refine orderOf_eq_prime ?_ (proj_ne_one_of (Or.inl t01))
    rw [← map_pow, proj_eq_one_iff, sq]
    exact ⟨-1, u4, by rw [coe_mul4]; exact tt⟩
  have hct : proj 4 (ZMod 3) cSL * proj 4 (ZMod 3) tSL =
      proj 4 (ZMod 3) tSL * proj 4 (ZMod 3) cSL := by
    have e : cSL * tSL = tSL * cSL := Subtype.ext (by rw [coe_mul4, coe_mul4]; exact ct)
    have := congrArg (proj 4 (ZMod 3)) e
    rwa [map_mul, map_mul] at this
  have hc3' : cSL * (cSL * cSL) = 1 :=
    Subtype.ext (by rw [coe_mul4, coe_mul4, coe_one4]; exact c3)
  have hcinv : cSL⁻¹ = cSL * cSL := inv_eq_of_mul_eq_one_right hc3'
  have hdcd : dSL * cSL * dSL = cSL * cSL :=
    Subtype.ext (by rw [coe_mul4, coe_mul4, coe_mul4]; exact dcd)
  have hprod : proj 4 (ZMod 3) dSL * (proj 4 (ZMod 3) cSL * proj 4 (ZMod 3) dSL *
      (proj 4 (ZMod 3) cSL)⁻¹) = proj 4 (ZMod 3) cSL := by
    have key : dSL * (cSL * dSL * cSL⁻¹) = cSL := by
      rw [hcinv]
      calc dSL * (cSL * dSL * (cSL * cSL)) = dSL * cSL * dSL * cSL * cSL := by group
        _ = cSL * (cSL * (cSL * cSL)) := by rw [hdcd]; group
        _ = cSL := by rw [hc3', mul_one]
    have := congrArg (proj 4 (ZMod 3)) key
    rwa [map_mul, map_mul, map_mul, map_inv] at this
  have hc3 : orderOf (proj 4 (ZMod 3) cSL) = 3 := by
    refine orderOf_eq_prime ?_ (proj_ne_one_of (Or.inr c20))
    rw [← map_pow, show cSL ^ 3 = cSL * (cSL * cSL) by rw [pow_succ, pow_succ, pow_one, mul_assoc],
      hc3', map_one]
  refine hz.false_of_not_two hPC hPn hP2 htP ht2 hct ?_
  intro k hk
  rw [hprod, hc3] at hk
  rcases k with _ | k
  · norm_num at hk
  · rw [pow_succ] at hk
    omega

end AS35W

end CFSG.LargeExtraspecial
