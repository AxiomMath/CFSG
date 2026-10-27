module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalBlockRank
public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalTensor
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def symTwo (p q : K) : Matrix (Fin 3) (Fin 3) K :=
  !![p, q, 0; q, -p, 0; 0, 0, 0]

@[expose] def skewTwo : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; -1, 0, 0; 0, 0, 0]

@[expose] def rankTwoNilpotent (s : SL(2, K)) (p q : K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  tensorMatrix ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) (symTwo p q) +
    (3 : K) • tensorMatrix 1 skewTwo

theorem symTwo_mul_symTwo (p q : K) :
    symTwo p q * symTwo p q =
      (p ^ 2 + q ^ 2) • (diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symTwo, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> ring

theorem skewTwo_mul_skewTwo :
    (skewTwo : Matrix (Fin 3) (Fin 3) K) * skewTwo =
      (-1 : K) • (diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewTwo, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem symTwo_mul_skewTwo_add (p q : K) :
    symTwo p q * skewTwo + skewTwo * symTwo p q = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symTwo, skewTwo, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem symTwo_transpose (p q : K) : (symTwo p q)ᵀ = symTwo p q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symTwo]

theorem skewTwo_transpose : (skewTwo : Matrix (Fin 3) (Fin 3) K)ᵀ = -skewTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewTwo]

theorem diag_symTwo_skewTwo (p q : K) :
    (diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) K) * symTwo p q = symTwo p q ∧
    symTwo p q * (diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) K) = symTwo p q ∧
    (diagonal ![0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * symTwo p q = 0 ∧
    symTwo p q * (diagonal ![0, 0, 1] : Matrix (Fin 3) (Fin 3) K) = 0 ∧
    (diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) K) * skewTwo = skewTwo ∧
    skewTwo * (diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) K) = skewTwo ∧
    (diagonal ![0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * skewTwo = 0 ∧
    skewTwo * (diagonal ![0, 0, 1] : Matrix (Fin 3) (Fin 3) K) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [symTwo, skewTwo, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem rankTwoNilpotent_mul_self {s : SL(2, K)} (hs : IsCubeRootBlock s) {p q : K}
    (hpq : p ^ 2 + q ^ 2 = -3) : rankTwoNilpotent s p q * rankTwoNilpotent s p q = 0 := by
  have hPP : ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) *
      ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) =
        (-3 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← sq]
    exact hs.two_smul_add_one_sq
  set P : Matrix (Fin 2) (Fin 2) K := (2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1 with hP
  have h11 : tensorMatrix P (symTwo p q) * tensorMatrix P (symTwo p q) =
      (9 : K) • tensorMatrix 1 (diagonal ![1, 1, 0]) := by
    rw [tensorMatrix_mul, hPP, symTwo_mul_symTwo, hpq, tensorMatrix_smul_left,
      tensorMatrix_smul_right, smul_smul]
    norm_num
  have h12 : tensorMatrix P (symTwo p q) * tensorMatrix 1 skewTwo +
      tensorMatrix 1 skewTwo * tensorMatrix P (symTwo p q) = 0 := by
    rw [tensorMatrix_mul, tensorMatrix_mul, Matrix.mul_one, Matrix.one_mul,
      ← tensorMatrix_add_right, symTwo_mul_skewTwo_add, tensorMatrix_zero_right]
  have h22 : tensorMatrix (1 : Matrix (Fin 2) (Fin 2) K) skewTwo * tensorMatrix 1 skewTwo =
      (-1 : K) • tensorMatrix 1 (diagonal ![1, 1, 0]) := by
    rw [tensorMatrix_mul, Matrix.one_mul, skewTwo_mul_skewTwo, tensorMatrix_smul_right]
  unfold rankTwoNilpotent
  calc _ = tensorMatrix P (symTwo p q) * tensorMatrix P (symTwo p q) +
        (3 : K) • (tensorMatrix P (symTwo p q) * tensorMatrix 1 skewTwo +
          tensorMatrix 1 skewTwo * tensorMatrix P (symTwo p q)) +
        (9 : K) • (tensorMatrix 1 skewTwo * tensorMatrix 1 skewTwo) := by
        simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
        norm_num
        abel
    _ = 0 := by rw [h11, h12, h22]; module

theorem rankTwoNilpotent_adjoint {s : SL(2, K)} (hs : IsCubeRootBlock s) (p q : K) :
    (rankTwoNilpotent s p q)ᵀ * fromBlocks 0 1 (-1) 0 +
      fromBlocks 0 1 (-1) 0 * rankTwoNilpotent s p q = 0 := by
  have hadj := skewPart_adjoint hs
  set P : Matrix (Fin 2) (Fin 2) K := (2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1 with hP
  unfold rankTwoNilpotent
  rw [← hP, fromBlocks_form_eq_tensorMatrix]
  rw [Matrix.transpose_add, Matrix.transpose_smul, tensorMatrix_transpose, tensorMatrix_transpose,
    symTwo_transpose, skewTwo_transpose, Matrix.transpose_one]
  have e1 : tensorMatrix Pᵀ (symTwo p q) * tensorMatrix !![0, 1; -1, 0] 1 +
      tensorMatrix !![0, 1; -1, 0] 1 * tensorMatrix P (symTwo p q) = 0 := by
    rw [tensorMatrix_mul, tensorMatrix_mul, Matrix.mul_one, Matrix.one_mul,
      ← tensorMatrix_add_left, hadj, tensorMatrix_zero_left]
  have e2 : tensorMatrix (1 : Matrix (Fin 2) (Fin 2) K) (-skewTwo) *
      tensorMatrix !![0, 1; -1, 0] 1 +
      tensorMatrix !![0, 1; -1, 0] 1 * tensorMatrix 1 skewTwo = 0 := by
    rw [tensorMatrix_mul, tensorMatrix_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
      Matrix.one_mul, ← tensorMatrix_add_right, neg_add_cancel, tensorMatrix_zero_right]
  calc _ = (tensorMatrix Pᵀ (symTwo p q) * tensorMatrix !![0, 1; -1, 0] 1 +
      tensorMatrix !![0, 1; -1, 0] 1 * tensorMatrix P (symTwo p q)) +
      (3 : K) • (tensorMatrix (1 : Matrix (Fin 2) (Fin 2) K) (-skewTwo) *
        tensorMatrix !![0, 1; -1, 0] 1 +
      tensorMatrix !![0, 1; -1, 0] 1 * tensorMatrix 1 skewTwo) := by
        simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add]
        abel
    _ = 0 := by rw [e1, e2]; simp

theorem commute_blockMatrix_rankTwoNilpotent {s : SL(2, K)} (p q : K)
    {A A' : Matrix (Fin 2) (Fin 2) K} (hA : Commute A (s : Matrix (Fin 2) (Fin 2) K)) :
    Commute (blockMatrix ![A, A, A']) (rankTwoNilpotent s p q) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := diag_symTwo_skewTwo (K := K) p q
  have hAP : Commute A ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) :=
    (hA.smul_right 2).add_right (Commute.one_right A)
  unfold Commute SemiconjBy rankTwoNilpotent
  rw [blockMatrix_pair]
  generalize ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) = P at hAP ⊢
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, tensorMatrix_mul, h1, h2, h3, h4,
    h5, h6, h7, h8, tensorMatrix_zero_right, Matrix.mul_one, Matrix.one_mul, hAP.eq, smul_zero,
    add_zero]

theorem rankTwoNilpotent_offDiag_ne {s : SL(2, K)} (h6 : (6 : K) ≠ 0) (p q : K) :
    rankTwoNilpotent s p q (Sum.inl 0) (Sum.inl 1) ≠ 0 ∨
      rankTwoNilpotent s p q (Sum.inl 1) (Sum.inl 0) ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  apply h6
  simp [rankTwoNilpotent, tensorMatrix, symTwo, skewTwo] at h1 h2
  linear_combination h1 - h2

theorem rankTwoNilpotent_ne_zero {s : SL(2, K)} (h6 : (6 : K) ≠ 0) (p q : K) :
    rankTwoNilpotent s p q ≠ 0 := by
  intro h0
  rcases rankTwoNilpotent_offDiag_ne (s := s) h6 p q with h | h <;> exact h (by rw [h0]; rfl)

@[expose] noncomputable def rankTwoElement {s : SL(2, K)} (hs : IsCubeRootBlock s) {p q : K}
    (hpq : p ^ 2 + q ^ 2 = -3) : StatedSp 3 K :=
  unipotentSp (rankTwoNilpotent s p q) (rankTwoNilpotent_adjoint hs p q)
    (rankTwoNilpotent_mul_self hs hpq)

theorem orderOf_rankTwoElement {r : ℕ} (hr : r.Prime) [CharP K r] {s : SL(2, K)}
    (hs : IsCubeRootBlock s) {p q : K} (hpq : p ^ 2 + q ^ 2 = -3) (h6 : (6 : K) ≠ 0) :
    orderOf (rankTwoElement hs hpq) = r :=
  orderOf_unipotentSp hr _ _ _ (rankTwoNilpotent_ne_zero h6 p q)

theorem commute_block_rankTwoElement {s : SL(2, K)} (hs : IsCubeRootBlock s) {p q : K}
    (hpq : p ^ 2 + q ^ 2 = -3) {a a' : SL(2, K)}
    (ha : Commute (a : Matrix (Fin 2) (Fin 2) K) (s : Matrix (Fin 2) (Fin 2) K)) :
    Commute (block ![a, a, a']) (rankTwoElement hs hpq) := by
  rw [commute_iff_coe_commute, coe_block_vec]
  exact (Commute.one_right _).add_right (commute_blockMatrix_rankTwoNilpotent p q ha)

theorem rankTwoElement_not_mem_range_block {s : SL(2, K)} (hs : IsCubeRootBlock s) {p q : K}
    (hpq : p ^ 2 + q ^ 2 = -3) (h6 : (6 : K) ≠ 0) :
    rankTwoElement hs hpq ∉ (block : (Fin 3 → SL(2, K)) →* StatedSp 3 K).range := by
  rcases rankTwoNilpotent_offDiag_ne (s := s) h6 p q with h | h
  · refine not_mem_range_block_of_apply_ne (i := 0) (j := 1) (by decide) ?_
    simpa [rankTwoElement, coe_unipotentSp] using h
  · refine not_mem_range_block_of_apply_ne (i := 1) (j := 0) (by decide) ?_
    simpa [rankTwoElement, coe_unipotentSp] using h

theorem two_le_pRank_centralizer_c₀_weight_two [Finite K] {r : ℕ} (hr : r.Prime) [CharP K r]
    (h5 : 5 ≤ r) {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    2 ≤ CFSG.Open.pRank r (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 0])} : Set (StatedSp 3 K))) := by
  haveI := Fact.mk hr
  obtain ⟨p, q, hpq⟩ := exists_sq_add_sq_eq_neg_three (K := K) hr
  have h6 : (6 : K) ≠ 0 := six_ne_zero_of_five_le h5 hs.three_ne_zero
  have hτ := orderOf_unipotent_one (K := K) hr
  have hy : block (Pi.mulSingle 2 (CFSG.SL2MinimalFaithful.unipotent (1 : K))) ∈
      Subgroup.centralizer ({c₀ hs (Multiplicative.ofAdd ![1, 1, 0])} : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_block_mulSingle_c₀ (i := 2) hs (CFSG.SL2MinimalFaithful.unipotent (1 : K))
      (Multiplicative.ofAdd ![1, 1, 0]) (by simp)).eq
  have hc : Commute (block (Pi.mulSingle 2 (CFSG.SL2MinimalFaithful.unipotent (1 : K))))
      (rankTwoElement hs hpq) := by
    have e : block (Pi.mulSingle 2 (CFSG.SL2MinimalFaithful.unipotent (1 : K))) =
        block ![1, 1, CFSG.SL2MinimalFaithful.unipotent (1 : K)] := by
      congr 1
      funext i
      fin_cases i <;> simp
    rw [e]
    refine commute_block_rankTwoElement hs hpq (a := 1) ?_
    simpa using Commute.one_left (s : Matrix (Fin 2) (Fin 2) K)
  have hu : rankTwoElement hs hpq ∈
      Subgroup.centralizer ({c₀ hs (Multiplicative.ofAdd ![1, 1, 0])} : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, c₀_point_110]
    exact (commute_block_rankTwoElement hs hpq (a := s) (a' := 1) (Commute.refl _)).symm.eq
  have hz : Subgroup.zpowers
      (block (Pi.mulSingle 2 (CFSG.SL2MinimalFaithful.unipotent (1 : K)))) ≤
        (block : (Fin 3 → SL(2, K)) →* StatedSp 3 K).range :=
    Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hn : rankTwoElement hs hpq ∉ Subgroup.zpowers
      (block (Pi.mulSingle 2 (CFSG.SL2MinimalFaithful.unipotent (1 : K)))) := fun hmem =>
    rankTwoElement_not_mem_range_block hs hpq h6 (hz hmem)
  exact CFSG.GroupTheory.two_le_pRank_of_commute hy hu
    (by rw [orderOf_block_mulSingle, hτ]) (orderOf_rankTwoElement hr hs hpq h6) hc hn

theorem one_le_pRank_centralizer_c₀_planeB [Finite K] {r : ℕ} (hr : r.Prime) [CharP K r]
    (h5 : 5 ≤ r) {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    1 ≤ CFSG.Open.pRank r (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 1]), c₀ hs (Multiplicative.ofAdd ![0, 0, 1])} :
        Set (StatedSp 3 K))) := by
  obtain ⟨p, q, hpq⟩ := exists_sq_add_sq_eq_neg_three (K := K) hr
  have h6 : (6 : K) ≠ 0 := six_ne_zero_of_five_le h5 hs.three_ne_zero
  refine one_le_pRank_of_mem_of_orderOf_eq hr (x := rankTwoElement hs hpq) ?_
    (orderOf_rankTwoElement hr hs hpq h6)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | rfl
  · rw [c₀_point_111]
    exact (commute_block_rankTwoElement hs hpq (a := s) (a' := s) (Commute.refl _)).eq
  · rw [c₀_point_001]
    refine (commute_block_rankTwoElement hs hpq (a := 1) (a' := s) ?_).eq
    simpa using Commute.one_left (s : Matrix (Fin 2) (Fin 2) K)

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
