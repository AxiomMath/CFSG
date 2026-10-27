module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalWeightTwoPair
public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalBlockRank
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def weightTwoMat (s z : SL(2, K)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  weightTwoConj s * tensorMatrix 1 (leviMat z) * weightTwoConjInv s

theorem weightTwoMat_one [CharP K 2] (s : SL(2, K)) : weightTwoMat s 1 = 1 := by
  rw [weightTwoMat, leviMat_one, tensorMatrix_one, Matrix.mul_one, weightTwoConj_mul_inv]

theorem weightTwoMat_mul [CharP K 2] (s z w : SL(2, K)) :
    weightTwoMat s (z * w) = weightTwoMat s z * weightTwoMat s w := by
  have h : tensorMatrix (1 : Matrix (Fin 2) (Fin 2) K) (leviMat (z * w)) =
      tensorMatrix 1 (leviMat z) * tensorMatrix 1 (leviMat w) := by
    rw [tensorMatrix_mul, Matrix.one_mul, leviMat_mul]
  simp only [weightTwoMat, h, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (weightTwoConjInv s) (weightTwoConj s), weightTwoConjInv_mul,
    Matrix.one_mul]

theorem transpose_weightTwoMat_mul [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s)
    (z : SL(2, K)) :
    (weightTwoMat s z)ᵀ * fromBlocks 0 1 (-1) 0 * weightTwoMat s z = fromBlocks 0 1 (-1) 0 := by
  have hM : (tensorMatrix 1 (leviMat z))ᵀ * tensorMatrix !![0, 1; -1, 0] leviForm *
      tensorMatrix 1 (leviMat z) = tensorMatrix !![0, 1; -1, 0] leviForm := by
    rw [tensorMatrix_transpose, Matrix.transpose_one, tensorMatrix_mul, tensorMatrix_mul,
      Matrix.one_mul, Matrix.mul_one, transpose_leviMat_mul_leviForm_mul]
  calc (weightTwoMat s z)ᵀ * fromBlocks 0 1 (-1) 0 * weightTwoMat s z
      = (weightTwoConjInv s)ᵀ * ((tensorMatrix 1 (leviMat z))ᵀ *
          ((weightTwoConj s)ᵀ * fromBlocks 0 1 (-1) 0 * weightTwoConj s) *
          tensorMatrix 1 (leviMat z)) * weightTwoConjInv s := by
        simp only [weightTwoMat, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (weightTwoConjInv s)ᵀ * ((weightTwoConj s)ᵀ * fromBlocks 0 1 (-1) 0 * weightTwoConj s) *
          weightTwoConjInv s := by rw [transpose_weightTwoConj_mul hs, hM]
    _ = (weightTwoConj s * weightTwoConjInv s)ᵀ * fromBlocks 0 1 (-1) 0 *
          (weightTwoConj s * weightTwoConjInv s) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = fromBlocks 0 1 (-1) 0 := by
        rw [weightTwoConj_mul_inv, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem commute_blockMatrix_weightTwoMat (s : SL(2, K)) {A : Matrix (Fin 2) (Fin 2) K}
    (hA : Commute A (s : Matrix (Fin 2) (Fin 2) K)) (A' : Matrix (Fin 2) (Fin 2) K)
    (z : SL(2, K)) : Commute (blockMatrix ![A, A, A']) (weightTwoMat s z) :=
  ((commute_blockMatrix_weightTwoConj s hA A').mul_right
    (commute_blockMatrix_tensorMatrix_leviMat A A' z)).mul_right
    (commute_blockMatrix_weightTwoConjInv s hA A')

theorem eq_one_of_weightTwoMat_eq_blockMatrix [CharP K 2] {s z : SL(2, K)}
    {A' : Matrix (Fin 2) (Fin 2) K} (h : weightTwoMat s z = blockMatrix ![1, 1, A']) : z = 1 := by
  have hc := commute_blockMatrix_weightTwoConj s
    (Commute.one_left (s : Matrix (Fin 2) (Fin 2) K)) A'
  have hM : tensorMatrix 1 (leviMat z) = blockMatrix ![1, 1, A'] := by
    calc tensorMatrix 1 (leviMat z)
        = weightTwoConjInv s * weightTwoMat s z * weightTwoConj s := by
          simp only [weightTwoMat, ← Matrix.mul_assoc, weightTwoConjInv_mul, Matrix.one_mul]
          rw [Matrix.mul_assoc, weightTwoConjInv_mul, Matrix.mul_one]
      _ = blockMatrix ![1, 1, A'] := by
          rw [h, Matrix.mul_assoc, hc.eq, ← Matrix.mul_assoc, weightTwoConjInv_mul,
            Matrix.one_mul]
  have h00 := congrFun (congrFun hM (Sum.inl 0)) (Sum.inl 0)
  have h01 := congrFun (congrFun hM (Sum.inl 0)) (Sum.inl 1)
  have h10 := congrFun (congrFun hM (Sum.inl 1)) (Sum.inl 0)
  have h11 := congrFun (congrFun hM (Sum.inl 1)) (Sum.inl 1)
  simp [tensorMatrix, blockMatrix, leviMat] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

@[expose] noncomputable def weightTwoSL [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    SL(2, K) →* StatedSp 3 K where
  toFun z := mkSp (weightTwoMat s z) (weightTwoMat s z⁻¹)
    (by rw [← weightTwoMat_mul, mul_inv_cancel, weightTwoMat_one])
    (by rw [← weightTwoMat_mul, inv_mul_cancel, weightTwoMat_one])
    (transpose_weightTwoMat_mul hs z)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact weightTwoMat_one s
  map_mul' z w := by
    apply Subtype.ext
    apply Units.ext
    exact weightTwoMat_mul s z w

theorem coe_weightTwoSL [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s) (z : SL(2, K)) :
    (((weightTwoSL hs z : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = weightTwoMat s z :=
  rfl

theorem weightTwoSL_injective [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    Function.Injective (weightTwoSL hs) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have h := congrArg (fun g : StatedSp 3 K => (((g : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))) hz
  refine eq_one_of_weightTwoMat_eq_blockMatrix (s := s) (A' := 1) ?_
  rw [blockMatrix_vec_const, tensorMatrix_one]
  exact h

theorem orderOf_weightTwoSL [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s) (z : SL(2, K)) :
    orderOf (weightTwoSL hs z) = orderOf z :=
  orderOf_injective _ (weightTwoSL_injective hs) z

private theorem wt2_mulSingle_two (g : SL(2, K)) : Pi.mulSingle (2 : Fin 3) g = ![1, 1, g] := by
  funext i
  fin_cases i <;> simp

theorem commute_c₀_point_110_weightTwoSL [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s)
    (z : SL(2, K)) : Commute (c₀ hs (Multiplicative.ofAdd ![1, 1, 0])) (weightTwoSL hs z) := by
  rw [commute_iff_coe_commute, c₀_point_110, coe_block_vec, coe_weightTwoSL,
    Matrix.SpecialLinearGroup.coe_one]
  exact commute_blockMatrix_weightTwoMat s (Commute.refl _) 1 z

theorem commute_block_mulSingle_two_weightTwoSL [CharP K 2] {s : SL(2, K)}
    (hs : IsCubeRootBlock s) (g z : SL(2, K)) :
    Commute (block (Pi.mulSingle 2 g)) (weightTwoSL hs z) := by
  rw [commute_iff_coe_commute, wt2_mulSingle_two, coe_block_vec, coe_weightTwoSL,
    Matrix.SpecialLinearGroup.coe_one]
  exact commute_blockMatrix_weightTwoMat s (Commute.one_left _) _ z

theorem weightTwoSL_not_mem_zpowers [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s)
    {z : SL(2, K)} (hz : z ≠ 1) :
    weightTwoSL hs z ∉ Subgroup.zpowers (block (Pi.mulSingle 2 z)) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← map_zpow, ← Pi.mulSingle_zpow, wt2_mulSingle_two] at hk
  have h := congrArg (fun g : StatedSp 3 K => (((g : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))) hk
  simp only [coe_block_vec, coe_weightTwoSL, Matrix.SpecialLinearGroup.coe_one] at h
  exact hz (eq_one_of_weightTwoMat_eq_blockMatrix h.symm)

theorem one_le_pRank_centralizer_c₀_planeA_of_dvd [Finite K] {s : SL(2, K)}
    (hs : IsCubeRootBlock s) {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K ^ 2 - 1) :
    1 ≤ CFSG.Open.pRank p (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 0, 0]), c₀ hs (Multiplicative.ofAdd ![0, 1, 0])} :
        Set (StatedSp 3 K))) := by
  obtain ⟨z, hz⟩ := exists_orderOf_eq_specialLinearGroup hp hpq
  refine one_le_pRank_of_mem_of_orderOf_eq hp (x := block (Pi.mulSingle 2 z)) ?_
    (by rw [orderOf_block_mulSingle, hz])
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | rfl
  · exact (commute_block_mulSingle_c₀ hs _ _ (by simp)).symm.eq
  · exact (commute_block_mulSingle_c₀ hs _ _ (by simp)).symm.eq

theorem two_le_pRank_centralizer_c₀_weight_one_of_dvd [Finite K] {s : SL(2, K)}
    (hs : IsCubeRootBlock s) {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 0, 0])} : Set (StatedSp 3 K))) := by
  obtain ⟨z, hz⟩ := exists_orderOf_eq_specialLinearGroup hp hpq
  have hmem : ∀ i : Fin 3, i ≠ 0 → block (Pi.mulSingle i z) ∈
      Subgroup.centralizer ({c₀ hs (Multiplicative.ofAdd ![1, 0, 0])} : Set (StatedSp 3 K)) := by
    intro i hi
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_block_mulSingle_c₀ (i := i) hs z (Multiplicative.ofAdd ![1, 0, 0])
      (by fin_cases i <;> simp_all)).eq
  exact two_le_pRank_of_block_mulSingle hp hz (i := 1) (j := 2) (by decide)
    (hmem 1 (by decide)) (hmem 2 (by decide))

theorem two_le_pRank_centralizer_c₀_weight_two_of_charTwo [Finite K] [CharP K 2]
    {s : SL(2, K)} (hs : IsCubeRootBlock s) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 0])} : Set (StatedSp 3 K))) := by
  have := Fact.mk hp
  obtain ⟨z, hz⟩ := exists_orderOf_eq_specialLinearGroup hp hpq
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact hp.one_lt.ne hz
  refine CFSG.GroupTheory.two_le_pRank_of_commute (x := block (Pi.mulSingle 2 z))
    (y := weightTwoSL hs z) ?_ ?_ (by rw [orderOf_block_mulSingle, hz])
    (by rw [orderOf_weightTwoSL, hz]) (commute_block_mulSingle_two_weightTwoSL hs z z)
    (weightTwoSL_not_mem_zpowers hs hz1)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_block_mulSingle_c₀ hs z _ (by simp)).eq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_point_110_weightTwoSL hs z).symm.eq

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
